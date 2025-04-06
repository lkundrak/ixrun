/*
 * PC/IX Emulator
 * Copyright (C) 2025  Lubomir Rintel <lkundrak@v3.sk>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */


#define _GNU_SOURCE

#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/utsname.h>
#include <sys/wait.h>

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <utime.h>
#include <termios.h>

#include <x86emu.h>

/* Max argv[] and envp[] sizes, chosen arbitrarily and lazily. */
static const int strc = 128;

static const char interp[] = "/bin/sh";

static const uint16_t code_seg = 0x3000;
static const uint16_t data_seg = 0x5000;
static uint8_t *code;
static uint8_t *data;

struct aout {
	uint8_t a_magic[2];
	uint8_t a_flags;
	uint8_t a_cpu;
	uint8_t a_hdrlen;
	uint8_t a_resvd;
	uint16_t a_version;
	uint32_t a_text;
	uint32_t a_data;
	uint32_t a_bss;
	uint32_t a_entry;
	uint32_t a_stack;
	uint32_t a_syms;
};

static uint16_t
sdata (uint8_t *mem, long sp, const void *buf, int len)
{
	if (sp < len)
		return -1;

	sp -= len;
	sp &= 0xffff;

	memcpy (&mem[sp], buf, len);
	return sp;
}

static inline uint16_t
sstr (uint8_t *mem, long sp, const char *str)
{
	return sdata (mem, sp, str, strlen (str) + 1);
}

static inline uint16_t
sint (uint8_t *mem, long sp, uint16_t val)
{
	uint16_t val_le16 = htole16 (val);

	return sdata (mem, sp, &val_le16, sizeof (val_le16));
}

static FILE *
open_binary (const char *pathname, struct aout *hdr)
{
	FILE *inf = NULL;
	int ret;

	inf = fopen(pathname, "rb");
	if (inf == NULL)
		return NULL;

	ret = fread(hdr, sizeof (*hdr), 1, inf);
	if (ret != 1) {
		if (feof(inf))
			errno = 0;
		goto error;
	}

	if (hdr->a_magic[0] != 0x01 || hdr->a_magic[1] != 0x03) {
		errno = 0;
		goto error;
	}

	return inf;
error:
	fclose (inf);
	return NULL;
}

static int
execme (x86emu_t *emu, const char *pathname, char *const argv[], char *const envp[])
{
	uint8_t *new_code = NULL;
	uint8_t *new_data = NULL;
	uint16_t tenvp[strc];
	uint16_t targv[strc];
	FILE *inf = NULL;
	struct aout hdr;
	int use_interp;
	int argc;
	int envc;
	long sp;
	int ret;
	int i;

	for (argc = 0; argv[argc] != NULL; argc++) {
		if (argc == strc - 2) {
			/* Leave room for interpreter and sentinel. */
			x86emu_log (emu, "Too many arguments.\n");
			errno = ENOMEM;
			return -1;
		}
	}

	for (envc = 0; envp[envc] != NULL; envc++) {
		if (envc == strc - 1) {
			/* Leave room for sentinel. */
			x86emu_log (emu, "Too many variables.\n");
			errno = ENOMEM;
			return -1;
		}
	}

	inf = open_binary (pathname, &hdr);
	if (inf == NULL && errno == 0) {
		inf = open_binary (interp, &hdr);
		use_interp = 1;
	} else {
		use_interp = 0;
	}
	if (inf == NULL) {
		if (errno == 0)
			errno = ENOEXEC;
		return -1;
	}

	if (hdr.a_cpu != 0x04) {
		x86emu_log (emu, "%s: %s\n", pathname, "Not 8086");
		errno = ENOEXEC;
		goto error;
	}

	ret = fseek(inf, hdr.a_hdrlen, SEEK_SET);
	if (ret == -1)
		goto error;

	sp = le32toh(hdr.a_stack);
	/* Always use as much stack as possible, modern systems are going
	 * to waste a lot of it with the environment block... */
	sp = 0x10000;

	switch (hdr.a_flags) {
	case 0x10:
		if (sp < le32toh(hdr.a_text) + le32toh(hdr.a_data)) {
			x86emu_log (emu, "Text+data won't fit in heap.\n");
			errno = ENOEXEC;
			goto error;
		}

		new_code = calloc (1, sp);
		new_data = new_code;
		if (new_code == NULL)
			goto error;

		ret = fread(new_code, le32toh(hdr.a_text) + le32toh(hdr.a_data), 1, inf);
		if (ret != 1) {
			if (feof(inf)) {
				x86emu_log (emu, "%s: %s\n", pathname, "Short read");
				errno = EFAULT;
			}
			goto error;
		}

		break;

	case 0x70:
		if (sp < le32toh(hdr.a_data)) {
			x86emu_log (emu, "Data won't fit in heap.\n");
			errno = ENOEXEC;
			goto error;
		}

		new_code = calloc (1, le32toh(hdr.a_text));
		if (new_code == NULL)
			goto error;

		new_data = calloc (1, sp);
		if (new_data == NULL)
			goto error;

		ret = fread(new_code, le32toh(hdr.a_text), 1, inf);
		if (ret != 1) {
			if (feof(inf)) {
				x86emu_log (emu, "%s: %s\n", pathname, "Short read");
				errno = EFAULT;
			}
			goto error;
		}

		ret = fread(new_data, le32toh(hdr.a_data), 1, inf);
		if (ret != 1) {
			if (feof(inf)) {
				x86emu_log (emu, "%s: %s\n", pathname, "Short read");
				errno = EFAULT;
			}
			goto error;
		}

		break;

	default:
		errno = ENOEXEC;
		goto error;
	}

	ret = fclose (inf);
	inf = NULL;
	if (ret == -1)
		goto error;

	/*
	 * Set up initial stack.
	 */

	/* sentinel */
	sp = sdata (new_data, sp, "\0", 2);

	/* envp[] */
	for (i = 0; i < envc; i++) {
		sp = sstr (new_data, sp, envp[i]);
		tenvp[i] = sp;
	}
	tenvp[i] = 0;

	/* argv[] */
	if (use_interp) {
		sp = sstr (new_data, sp, interp);
		targv[0] = sp;
		sp = sstr (new_data, sp, pathname);
		targv[1] = sp;
	}
	for (i = use_interp; i < argc; i++) {
		sp = sstr (new_data, sp, argv[i]);
		targv[i + use_interp] = sp;
	}
	targv[i + use_interp] = 0;

	/* envp */
	for (i = envc; i >= 0; i--)
		sp = sint (new_data, sp, tenvp[i]);

	/* argv */
	for (i = argc + use_interp; i >= 0; i--)
		sp = sint (new_data, sp, targv[i]);

	/* argc */
	sp = sint (new_data, sp, argc + use_interp);

	if (sp == -1) {
		errno = ENOMEM;
		goto error;
	}

	/*
	 * Replace the process.
	 *
	 * No failures permitted below this point, no modifications
	 * to the original process above.
	 */

	ret = 0;

	free (code);
	if (code != data)
		free (data);
	code = new_code;
	data = new_data;

	x86emu_set_seg_register(emu, emu->x86.R_CS_SEL, code_seg);
	if (code == data) {
		x86emu_set_seg_register(emu, emu->x86.R_DS_SEL, code_seg);
		x86emu_set_seg_register(emu, emu->x86.R_SS_SEL, code_seg);
		x86emu_set_seg_register(emu, emu->x86.R_ES_SEL, code_seg);
	} else {
		x86emu_set_seg_register(emu, emu->x86.R_DS_SEL, data_seg);
		x86emu_set_seg_register(emu, emu->x86.R_SS_SEL, data_seg);
		x86emu_set_seg_register(emu, emu->x86.R_ES_SEL, data_seg);
	}
	emu->x86.R_IP = le32toh(hdr.a_entry);
	emu->x86.R_SP = sp;
	x86emu_log(emu, "Process %d starting execution of '%s'%s%s%s\n",
		getpid(), pathname,
		use_interp ? " via'" : "",
		use_interp ? interp : "",
		use_interp ? "\"" : "");
	return 0;

error:
	x86emu_clear_log (emu, 1);
	if (inf) {
		if (fclose(inf) != 0)
			abort ();
	}

	free (new_code);
	if (new_code != new_data)
		free (new_data);

	return -1;
}

static inline uint16_t
arg (x86emu_t *emu, int i)
{
	return le16toh(*(uint16_t *)&data[emu->x86.R_SP + i * 2]);
}

static inline char *
filename (void *adr)
{
	return strdup ((char *)adr);
}

static int
signum (uint16_t sig)
{
	switch (sig) {
	case 0: return 0; break;
	case 1: return SIGHUP; break;
	case 2: return SIGINT; break;
	case 3: return SIGQUIT; break;
	case 4: return SIGILL; break;
	case 5: return SIGTRAP; break;
	case 6: return SIGIOT; break;
	case 8: return SIGFPE; break;
	case 9: return SIGKILL; break;
	case 10: return SIGBUS; break;
	case 11: return SIGSEGV; break;
	case 12: return SIGSYS; break;
	case 13: return SIGPIPE; break;
	case 14: return SIGALRM; break;
	case 15: return SIGTERM; break;
	case 16: return SIGUSR1; break;
	case 17: return SIGUSR2; break;
	case 18: return SIGCLD; break;
	case 19: return SIGPWR; break;
	case 7: /* SIGEMT */
	default:
		errno = EINVAL;
		return -1;
	};
}

static void
setstat (void *adr, struct stat *st)
{
	*(uint16_t *)(adr + 0) = htole16(st->st_dev);
	*(uint16_t *)(adr + 2) = htole16(st->st_ino);
	*(uint16_t *)(adr + 4) = htole16(st->st_mode);
	*(int16_t *)(adr + 6) = htole16(st->st_nlink);
	*(uint16_t *)(adr + 8) = htole16(st->st_uid);
	*(uint16_t *)(adr + 10) = htole16(st->st_gid);
	*(uint16_t *)(adr + 12) = htole16(st->st_rdev);
	*(uint32_t *)(adr + 14) = htole32(st->st_size);
	*(uint32_t *)(adr + 18) = htole32(st->st_atime);
	*(uint32_t *)(adr + 22) = htole32(st->st_mtime);
	*(uint32_t *)(adr + 26) = htole32(st->st_ctime);
}

static int
dirf (int fd)
{
	struct dirent *ent;
	int ofd = -1;
	int nfd = -1;
	DIR *dir;
	int ret;

	ret = dup (fd);
	if (ret == -1)
		goto out;
	ofd = ret;

	ret = memfd_create ("dirf", 0);
	if (ret == -1)
		goto out;
	nfd = ret;

	ret = dup2 (nfd, fd);
	if (ret == -1)
		goto out;

	dir = fdopendir (ofd);
	if (dir == NULL) {
		ret = -1;
		goto out;
	}
	while ((ent = readdir (dir)) != NULL) {
		uint8_t dirent[16];

		*(uint16_t *)&dirent[0] = htole16 (ent->d_ino);
		memcpy (&dirent[2], ent->d_name, 13);
		dirent[15] = '\0';

		ret = write (nfd, dirent, sizeof (dirent));
		if (ret != sizeof (dirent)) {
			errno = EIO;
			break;
		}
	}
	closedir (dir);
	ofd = -1;
	if (errno) {
		ret = -1;
		goto out;
	}

	ret = lseek(nfd, 0, SEEK_SET);
	if (ret == -1)
		goto out;

out:
	if (ofd != -1)
		close (ofd);
	if (nfd != -1)
		close (nfd);
	return ret;
}

int fpu_handler (x86emu_t *emu, uint16_t insn);

static int
int_handler (x86emu_t *emu, u8 num, unsigned type)
{
	char *nm = NULL;
	union {
		struct utsname ubuf;
		struct stat st;
		mode_t mode;
		int sig;
		int pipes[2];
		int wstat;
		struct utimbuf utm;
		char *nm;
		struct termios tio;
	} u;
	long ret = -1;
	uint16_t insn;

	x86emu_clear_log (emu, 1);
	if (num == 6 && type == (INTR_MODE_RESTART | INTR_TYPE_FAULT)) {
		insn = x86emu_read_word(emu, (code_seg << 4) + emu->x86.R_IP - 2);
		if ((insn & 0xf800) == 0xd800) {
			x86emu_log (emu, "ESC 0x%04x at 0x%04x\n", insn, emu->x86.R_IP);
			fprintf (stderr, "ESC 0x%04x at 0x%04x\n", insn, emu->x86.R_IP);
			abort();

			/* Just ignore ESC, we got no coprocessor */
			return 1;
		}
		fprintf(stderr, "invalid insn 0x%x before 0x%x\n", insn, emu->x86.R_IP);
		abort();
		return 0;
	}

	if (num == 13 && type == (INTR_MODE_ERRCODE | INTR_MODE_RESTART | INTR_TYPE_FAULT)) {
		fprintf(stderr, "protection error before 0x%x\n", emu->x86.R_IP);
		x86emu_clear_log (emu, 1);
		return 1;
	}

	if (type != INTR_TYPE_SOFT) {
		fprintf(stderr, "int %d type 0x%x\n", num, type);
		return 0;
	}
	if ((num & 0x80) == 0) {
		fprintf(stderr, "trap %d type 0x%x\n", num, type);
		return 0;
	}

	if ((num & 0xf8) == 0xd8) {
		//fprintf(stderr, "fpu %d type 0x%x\n", num, type);
		insn = num << 8;
		insn |= x86emu_read_byte(emu, (code_seg << 4) + emu->x86.R_IP);
		emu->x86.R_IP++;
		return fpu_handler (emu, insn);
	}

	errno = 0;
	switch (num & 0x7f) {
	case 0x01:
		x86emu_log (emu, "SYS exit (status: %d, unused heap: %d)",
			arg (emu, 1), arg (emu, 2));
		x86emu_clear_log (emu, 1);
		fflush(stderr);
		exit (arg (emu, 1));

	case 0x02:
		x86emu_log (emu, "SYS fork\n");
		x86emu_clear_log (emu, 1);
		fflush(stderr);
		ret = fork();
		/* Original process continues a bit further. */
		if (ret != 0)
			emu->x86.R_EIP += 2;
		break;

	case 0x03:
		x86emu_log (emu, "SYS read\n");
		ret = read (arg (emu, 1), &data[arg (emu, 2)], arg (emu, 3));

		if (errno == EISDIR) {
			/* Clear the error. */
			errno = 0;

			/* Replace file descriptor with legacy directory. */
			ret = dirf (arg (emu, 1));
			if (ret == -1)
				break;

			/* Retry the read now. */
			ret = read (arg (emu, 1), &data[arg (emu, 2)], arg (emu, 3));
		}

		break;

	case 0x04:
		x86emu_log (emu, "SYS write (%d, 0x%04x, %d)\n",
			arg (emu, 1), arg (emu, 2), arg (emu, 3));
		ret = write (arg (emu, 1), &data[arg (emu, 2)], arg (emu, 3));
		break;

	case 0x05:
		x86emu_log (emu, "SYS open\n");

		x86emu_clear_log (emu, 1);
		switch (arg (emu, 2) & 0x03) {
		case 0: u.mode = O_RDONLY; break;
		case 1: u.mode = O_WRONLY; break;
		case 2: u.mode = O_RDWR; break;
		default: abort ();
		}

		if (arg (emu, 2) & 0x04)
			u.mode |= O_NONBLOCK;
		if (arg (emu, 2) & 0x08)
			u.mode |= O_APPEND;
		if (arg (emu, 2) & 0x20)
			u.mode |= O_CREAT;
		if (arg (emu, 2) & 0x40)
			u.mode |= O_TRUNC;
		if (arg (emu, 2) & 0x80)
			u.mode |= O_EXCL;

		nm = filename (&data[arg (emu, 1)]);
		ret = open (nm, u.mode);
		break;

	case 0x06:
		x86emu_log (emu, "SYS close (%d)\n", arg (emu, 1));
		if (arg (emu, 1) == 2)
			ret = 0;
		else
			ret = close (arg (emu, 1));
		break;

	case 0x07:
		x86emu_log (emu, "SYS wait\n");
		ret = wait(&u.wstat);
		if (ret == -1)
			break;
		*(uint16_t *)&data[arg (emu, 1)] = htole16 (u.wstat);
		break;

	case 0x08:
		x86emu_log (emu, "SYS creat\n");
		nm = filename (&data[arg (emu, 1)]);
		ret = creat (nm, arg (emu, 2));
		break;

	case 0x09:
		x86emu_log (emu, "SYS link\n");

		u.nm = (char *)&data[arg (emu, 1)];
		if (u.nm[0] == '.' && u.nm[1] == '\0') {
			/* mkdir: Hardlinking '.' to './<newdir>/..' */
			ret = 0;
			break;
		}

		nm = (char *)&data[arg (emu, 2)];
		if (strlen (u.nm) + 2 == strlen (nm)
			/* mkdir: Hardlinking '<newdir>' to '<newdir>/.' */
			&& memcmp (u.nm, nm, strlen (u.nm)) == 0
			&& nm[strlen(u.nm)] == '/'
			&& nm[strlen(u.nm) + 1] == '.') {
			ret = 0;
			nm = NULL;
			break;
		}

		nm = filename (&data[arg (emu, 1)]);
		u.nm = filename (&data[arg (emu, 2)]);
		ret = link (nm, u.nm);
		free (u.nm);
		break;

	case 0x0a:
		x86emu_log (emu, "SYS unlink\n");
		nm = filename (&data[arg (emu, 1)]);
		ret = unlink (nm);
		break;

	case 0x0c:
		x86emu_log (emu, "SYS chdir\n");
		nm = filename (&data[arg (emu, 1)]);
		ret = chdir (nm);
		break;

	case 0x0d:
		x86emu_log (emu, "SYS time\n");
		ret = time (0);
		if (arg (emu, 1) != 0)
			*(uint16_t *)&data[arg (emu, 1)] = htole16 (ret);
		break;

	case 0x0e:
		x86emu_log (emu, "SYS mknod\n");
		nm = filename (&data[arg (emu, 1)]);
		if ((arg (emu, 2) & 070000) == 040000)
			ret = mkdir (nm, arg (emu, 2));
		else
			ret = mknod (nm, arg (emu, 2), arg (emu, 3));
		break;

	case 0x0f:
		x86emu_log (emu, "SYS chmod\n");
		nm = filename (&data[arg (emu, 1)]);
		ret = chmod (nm, arg (emu, 2));
		break;

	case 0x10:
		x86emu_log (emu, "SYS chown\n");
		nm = filename (&data[arg (emu, 1)]);
		ret = chown (nm, arg (emu, 2), arg (emu, 3));
		break;

	case 0x12:
		x86emu_log (emu, "SYS stat\n");
		nm = filename (&data[arg (emu, 1)]);
		ret = stat (nm, &u.st);
		if (ret != 0)
			break;
		setstat (&data[arg (emu, 2)], &u.st);
		break;

	case 0x13:
		x86emu_log (emu, "SYS lseek (%d, 0x%x%x, %x)\n",
			arg (emu, 1), arg (emu, 3), arg (emu, 2), arg (emu, 4));
		ret = lseek (arg (emu, 1), arg (emu, 2) + (arg (emu, 3) << 16), arg (emu, 4));
		break;

	case 0x14:
		x86emu_log (emu, "SYS getpid\n");
		ret = getpid () & 0x7fff;
		break;

	case 0x15:
		fprintf (stderr, "SYS mount\n");
		errno = ENODEV;
		break;

	case 0x16:
		fprintf (stderr, "SYS umount\n");
		errno = ENODEV;
		break;

	case 0x17:
		x86emu_log (emu, "SYS setuid\n");
		ret = setuid (arg (emu, 1)) & 0x7fff;
		break;

	case 0x18:
		x86emu_log (emu, "SYS getuid\n");
		ret = getuid () & 0x7fff;
		break;

	case 0x19:
		fprintf (stderr, "SYS stime\n");
		errno = ENODEV;
		break;

	case 0x1a:
		fprintf (stderr, "SYS ptrace\n");
		errno = ENODEV;
		break;

	case 0x1b:
		x86emu_log (emu, "SYS alarm\n");
		ret = alarm (arg (emu, 1));
		break;

	case 0x1c:
		x86emu_log (emu, "SYS fstat\n");
		ret = fstat (arg (emu, 1), &u.st);
		if (ret != 0)
			break;

		setstat (&data[arg (emu, 2)], &u.st);
		break;

	case 0x1d:
		x86emu_log (emu, "SYS pause\n");
		ret = pause ();
		break;

	case 0x1e:
		x86emu_log (emu, "SYS utime\n");
		nm = filename (&data[arg (emu, 1)]);
		u.utm.actime = le32toh (*(uint32_t *)&data[arg (emu, 2)]);
		u.utm.modtime = le32toh (*(uint32_t *)&data[arg (emu, 2) + 4]);
		ret = utime (nm, &u.utm);
		if (ret == -1)
			break;
		*(uint32_t *)&data[arg (emu, 2)] = htole32 (u.utm.actime);
		*(uint32_t *)&data[arg (emu, 2) + 4] = htole32 (u.utm.modtime);
		break;

	case 0x21:
		x86emu_log (emu, "SYS access\n");
		nm = filename (&data[arg (emu, 1)]);
		ret = access (nm, arg (emu, 2));
		break;

	case 0x22:
		x86emu_log (emu, "SYS nice\n");
		ret = nice (arg (emu, 1));
		break;

	case 0x24:
		x86emu_log (emu, "SYS sync\n");
		sync();
		ret = 0;
		break;

	case 0x25:
		x86emu_log (emu, "SYS kill\n");
		u.sig = signum (arg (emu, 2));
		if ((getpid() & 0x7fff) == arg (emu, 1))
			ret = kill (getpid(), u.sig);
		else
			ret = kill ((int16_t)arg (emu, 1), u.sig);
		if (u.sig == -1)
			break;
		break;

	case 0x27:
		x86emu_log (emu, "SYS setpgrp\n");
		switch (arg (emu, 1)) {
		case 0:
			ret = getpgrp ();
			break;
		case 1:
			ret = setpgrp ();
			break;
		default:
			errno = EINVAL;
		}
		break;

	case 0x29:
		x86emu_log (emu, "SYS dup\n");
		ret = dup (arg (emu, 1));
		break;

	case 0x2a:
		x86emu_log (emu, "SYS pipe\n");
		ret = pipe(u.pipes);
		if (ret == -1)
			break;
		*(uint16_t *)(&data[arg (emu, 1)]) = htole16 (u.pipes[0]);
		*(uint16_t *)(&data[arg (emu, 1)] + 2) = htole16 (u.pipes[1]);
		break;

	case 0x2b:
		fprintf (stderr, "SYS times\n");
		errno = ENODEV;
		break;

	case 0x2c:
		fprintf (stderr, "SYS profil\n");
		errno = ENODEV;
		break;

	case 0x2d:
		fprintf (stderr, "SYS lockf\n");
		errno = ENODEV;
		break;

	case 0x2e:
		x86emu_log (emu, "SYS setgid\n");
		ret = setgid (arg (emu, 1));
		break;

	case 0x2f:
		x86emu_log (emu, "SYS getgid\n");
		ret = getgid ();
		break;

	case 0x30:
		x86emu_log (emu, "SYS signal\n");
		u.sig = signum (arg (emu, 1));
		if (u.sig == -1)
			break;
		if (arg (emu, 1) == 0) {
			ret = (long)signal (u.sig, SIG_DFL);
		} else if (arg (emu, 1) == 0) {
			ret = (long)signal (u.sig, SIG_IGN);
		} else {
			errno = EINVAL;
		}
		break;

	case 0x32:
		fprintf (stderr, "SYS halt\n");
		errno = ENODEV;
		break;

	case 0x33:
		fprintf (stderr, "SYS acct\n");
		errno = ENODEV;
		break;

	case 0x36:
		x86emu_log (emu, "SYS ioctl\n");
		switch (arg (emu, 2)) {

		case 0x5401:
			x86emu_log (emu, "SYS TCGETA (%d, %04x, %04x)\n", arg (emu, 1), arg (emu, 2), arg (emu, 3));
			ret = tcgetattr (arg (emu, 1), &u.tio);
			if (ret == -1)
				break;
			*(uint16_t *)&data[arg (emu, 3) + 0] = u.tio.c_iflag;
			*(uint16_t *)&data[arg (emu, 3) + 2] = u.tio.c_oflag;
			*(uint16_t *)&data[arg (emu, 3) + 4] = u.tio.c_cflag;
			*(uint16_t *)&data[arg (emu, 3) + 6] = u.tio.c_lflag;
			data[arg (emu, 3) + 8] = 0; // c_line
			data[arg (emu, 3) + 9] = u.tio.c_cc[VINTR];
			data[arg (emu, 3) + 10] = u.tio.c_cc[VQUIT];
			data[arg (emu, 3) + 11] = u.tio.c_cc[VERASE];
			data[arg (emu, 3) + 12] = u.tio.c_cc[VKILL];
			data[arg (emu, 3) + 13] = u.tio.c_cc[VEOF];
			data[arg (emu, 3) + 14] = u.tio.c_cc[VEOL];
			data[arg (emu, 3) + 15] = u.tio.c_cc[VMIN];
			data[arg (emu, 3) + 16] = u.tio.c_cc[VTIME];
			ret = 0;
			break;

		case 0x5403:
			x86emu_log (emu, "SYS TCSETAW (%d, %04x, %04x)\n", arg (emu, 1), arg (emu, 2), arg (emu, 3));
			x86emu_log (emu, " [%04x] c_iflag\n", *(uint16_t *)&data[arg (emu, 3) + 0]);
			x86emu_log (emu, " [%04x] c_oflag\n", *(uint16_t *)&data[arg (emu, 3) + 2]);
			x86emu_log (emu, " [%04x] c_cflag, 9600 local\n", *(uint16_t *)&data[arg (emu, 3) + 4]);
			x86emu_log (emu, " [%04x] c_lflag\n", *(uint16_t *)&data[arg (emu, 3) + 6]);
			x86emu_log (emu, " [%02x] c_line\n", data[arg (emu, 3) + 8]);
			x86emu_log (emu, " [%02x] VINTR\n", data[arg (emu, 3) + 9]);
			x86emu_log (emu, " [%02x] VQUIT\n", data[arg (emu, 3) + 10]);
			x86emu_log (emu, " [%02x] VERASE\n", data[arg (emu, 3) + 11]);
			x86emu_log (emu, " [%02x] VKILL\n", data[arg (emu, 3) + 12]);
			x86emu_log (emu, " [%02x] VEOF\n", data[arg (emu, 3) + 13]);
			x86emu_log (emu, " [%02x] VEOL\n", data[arg (emu, 3) + 14]);
			x86emu_log (emu, " [%02x] VMIN\n", data[arg (emu, 3) + 15]);
			x86emu_log (emu, " [%02x] VTIME\n", data[arg (emu, 3) + 16]);
			ret = tcgetattr (arg (emu, 1), &u.tio);
			if (ret == -1)
				break;
			u.tio.c_iflag = *(uint16_t *)&data[arg (emu, 3) + 0];
			u.tio.c_oflag = *(uint16_t *)&data[arg (emu, 3) + 2];
			u.tio.c_cflag = *(uint16_t *)&data[arg (emu, 3) + 4];
			u.tio.c_lflag = *(uint16_t *)&data[arg (emu, 3) + 6];
			u.tio.c_cc[VINTR] = data[arg (emu, 3) + 9];
			u.tio.c_cc[VQUIT] = data[arg (emu, 3) + 10];
			u.tio.c_cc[VERASE] = data[arg (emu, 3) + 11];
			u.tio.c_cc[VKILL] = data[arg (emu, 3) + 12];
			u.tio.c_cc[VEOF] = data[arg (emu, 3) + 13];
			u.tio.c_cc[VEOL] = data[arg (emu, 3) + 14];
			u.tio.c_cc[VMIN] = data[arg (emu, 3) + 15];
			u.tio.c_cc[VTIME] = data[arg (emu, 3) + 16];
			ret = tcsetattr (arg (emu, 1), TCSADRAIN, &u.tio);
			break;

		default:
			fprintf (stderr, "SYS ioctl (%d, %04x, %04x)\n", arg (emu, 1), arg (emu, 2), arg (emu, 3));
			errno = ENODEV;
		}

		break;

	case 0x39:
		switch (arg (emu, 3)) {
		case 0:
			x86emu_log (emu, "SYS uname\n");
			ret = uname (&u.ubuf);
			if (ret != 0)
				break;

			/* { "PC/IX", "SELF", "1.0", "std", "ibmpc-xt" } */
			u.ubuf.sysname[8] = '\0';
			u.ubuf.nodename[8] = '\0';
			u.ubuf.release[8] = '\0';
			u.ubuf.version[8] = '\0';
			u.ubuf.machine[8] = '\0';

			memcpy (&data[arg (emu, 1) + 0], u.ubuf.sysname, 9);
			memcpy (&data[arg (emu, 1) + 9], u.ubuf.nodename, 9);
			memcpy (&data[arg (emu, 1) + 18], u.ubuf.release, 9);
			memcpy (&data[arg (emu, 1) + 27], u.ubuf.version, 9);
			memcpy (&data[arg (emu, 1) + 36], u.ubuf.machine, 9);
			break;
		case 2:
			fprintf (stderr, "SYS ustat\n");
			errno = ENODEV;
			break;
		default:
			errno = EINVAL;
		}
		break;

	case 0x3b:
		nm = filename (&data[arg (emu, 1)]);
		x86emu_log (emu, "SYS exece (%s)\n", nm);
		{
			uint16_t *targv = (uint16_t *)&data[arg (emu, 2)];
			uint16_t *tenvp = (uint16_t *)&data[arg (emu, 3)];
			char *cenvp[strc];
			char *cargv[strc];
			int i;

			for (i = 0; i < strc - 1 && targv[i] != 0; i++)
				cargv[i] = (char *)&data[targv[i]];
			cargv[i] = NULL;

			for (i = 0; i < strc - 1 && tenvp[i] != 0; i++)
				cenvp[i] = (char *)&data[tenvp[i]];
			cenvp[i] = NULL;

			ret = execme (emu, nm, cargv, cenvp);
		}
		break;

	case 0x3c:
		x86emu_log (emu, "SYS umask\n");
		ret = umask (arg (emu, 1));
		break;

	case 0x3d:
		x86emu_log (emu, "SYS chroot\n");
		nm = filename (&data[arg (emu, 1)]);
		ret = chroot (nm);
		break;

	case 0x3e:
		x86emu_log (emu, "SYS fcntl\n");
		if (arg (emu, 2) > 4) {
			errno = EINVAL;
			break;
		}
		ret = fcntl (arg (emu, 1), arg (emu, 2), arg (emu, 3));
		break;

	case 0x3f:
		fprintf (stderr, "SYS ulimit\n");
		errno = ENODEV;
		break;

	default:
		fprintf (stderr, "unimpl syscall %x\n", num);
		errno = EINVAL;
		abort();
		break;
	}

	if (errno) {
		emu->x86.R_AX = errno;
		emu->x86.R_FLG |= F_CF;
		if (errno == ENODEV) {
			fprintf (stderr, "INTH num=%08x type=%x\n", num, type);
			fprintf (stderr, " [1] %x\n", arg (emu, 1));
			fprintf (stderr, " [2] %x\n", arg (emu, 2));
			fprintf (stderr, " [3] %x\n", arg (emu, 3));
			abort();
		}
	} else {
		emu->x86.R_AX = ret;
		emu->x86.R_DX = ret >> 16;
		emu->x86.R_FLG &= ~F_CF;
	}
	free (nm);

	return 1;
}

static unsigned
io_handler (x86emu_t *emu, u32 const addr, u32 *val, unsigned const type)
{
	void *p;

	x86emu_clear_log (emu, 1);


	if ((type & ~0xff) == X86EMU_MEMIO_I) {
		fprintf(stderr, "bad in\n");
		abort();
		return 1;
	}
	if ((type & ~0xff) == X86EMU_MEMIO_O) {
		x86emu_log (emu, "out %x\n", addr);
		return 1;
	}

	if ((addr >= code_seg << 4) && (addr < (code_seg << 4) + 0x10000)) {
		p = &code[addr - (code_seg << 4)];
	} else if ((addr >= data_seg << 4) && (addr < (data_seg << 4) + 0x10000)) {
		p = &data[addr - (data_seg << 4)];
	} else {
		fprintf(stderr, "bad addr %x\n", addr);
		abort();
		return 1;
	}

	switch (type) {
	case X86EMU_MEMIO_X | X86EMU_MEMIO_8:
	case X86EMU_MEMIO_R | X86EMU_MEMIO_8:
		*val = *(uint8_t *)p;
		return 0;
	case X86EMU_MEMIO_X | X86EMU_MEMIO_16:
	case X86EMU_MEMIO_R | X86EMU_MEMIO_16:
		*val = *(uint16_t *)p;
		return 0;
	case X86EMU_MEMIO_X | X86EMU_MEMIO_32:
	case X86EMU_MEMIO_R | X86EMU_MEMIO_32:
		*val = *(uint32_t *)p;
		return 0;
	case X86EMU_MEMIO_W | X86EMU_MEMIO_8:
		*(uint8_t *)p = *val;
		return 0;
	case X86EMU_MEMIO_W | X86EMU_MEMIO_16:
		*(uint16_t *)p = *val;
		return 0;
	case X86EMU_MEMIO_W | X86EMU_MEMIO_32:
		*(uint32_t *)p = *val;
		return 0;
	default:
		fprintf(stderr, "bad io\n");
		abort();
	}
}

static void
flush_log (x86emu_t *emu, char *buf, unsigned size)
{
	char *eol;
	int end;

	if (emu->log.trace == 0)
		return;

	while (size) {
		eol = memchr(buf, '\n', size);
		if (eol != NULL)
			end = ++eol - buf;
		else
			end = size;
		if (fwrite (buf, end, 1, stderr) != 1) {
			perror ("write");
			return;
		}
		if (eol != NULL)
			fprintf (stderr, "[%d] ", getpid ());
		size -= end;
		buf += end;
	}
	fflush (stderr);
}

int
main(int argc, char *argv[], char *envp[])
{
	x86emu_t *emu;
	int ret;
	int opt;

	while ((opt = getopt(argc, argv, "+r:C:")) != -1) {
		switch (opt) {
		case 'r':
			ret = chroot (optarg);
			if (ret == -1) {
				perror(optarg);
				return -1;
			}
			break;
		case 'C':
			ret = chdir (optarg);
			if (ret == -1) {
				perror(optarg);
				return -1;
			}
			break;
		default:
			return -1;
		}
	}
	if ((argc - optind) < 1) {
		fprintf (stderr, "Usage: %s [-r <chroot>] [-C <chdir>] [--] <exec> [<args> ...]\n", argv[0]);
		return -1;
	}

	/*
	 * Prepare the emulator.
	 */

	emu = x86emu_new (0, 0);
	if (!emu) {
		fprintf(stderr, "no emu\n");
		abort();
	}

	x86emu_set_log(emu, 65535, flush_log);
	switch (atoi(getenv("PCIX_TRACE") ?: "")) {
	default:
	case 3: emu->log.trace |= X86EMU_TRACE_ACC;
	case 2: emu->log.trace |= X86EMU_TRACE_DEFAULT;
	case 1: emu->log.trace |= X86EMU_TRACE_CODE;
	case 0: break;
	}

	x86emu_set_intr_handler (emu, int_handler);
	x86emu_set_memio_handler(emu, io_handler);

	/*
	 * Execute the main program.
	 */

	ret = execme (emu, argv[optind], &argv[optind], envp);
	if (ret == -1) {
		perror (argv[optind]);
		return -1;
	}

	while (1) {
		ret = x86emu_run (emu, 0);
		x86emu_log (emu, "HALT.\n");
		x86emu_clear_log (emu, 1);
		if (ret != 0)
			break;
	}

	fprintf(stderr, "emu exit 0x%x\n", (unsigned)ret);
	abort();
}
