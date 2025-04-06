/*
 * Very incomplete 8087 library for PC/IX Emulator
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

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <math.h>

#include <x86emu.h>

static uint8_t
fetch_byte (x86emu_t *emu)
{
	return x86emu_read_byte (emu, emu->x86.R_CS_BASE + emu->x86.R_IP++);
}

long double st[8];
uint16_t sw = 0;

static inline uint8_t
top (int i)
{
	i += sw >> 11;
	return (unsigned)i % 8;
}

static inline void
pop (int i)
{
	int newtop = top(i) << 11;
	sw &= ~(7 << 11);
	sw |= newtop;
}

static void
dumpst(x86emu_t *emu)
{
	unsigned char *p;
	int i, n;

	for (i = 0; i < 8; i++) {
		x86emu_log (emu, "    [%d] ", i);

		p = (void *)&st[i];
		if (top(0) == i)
			x86emu_log (emu, " ST(0) --> ");
		else
			x86emu_log (emu, "           ");
		for (n = 0; n < 10; n++)
			x86emu_log (emu, " %02x", p[n]);

		x86emu_log (emu, "%f * 2^%d (%Lf)\n",
			significand(st[i]), ilogb(st[i]), st[i]);
	}
}

static uint32_t
fpu_ea (x86emu_t *emu, uint16_t insn)
{
	uint16_t mod = insn & 0x0c0;
	uint16_t rm = insn & 0x007;
	uint16_t disp;
	uint32_t ea;

	switch (mod) {
	case 0x00:
		disp = 0;
		break;
	case 0x40:
		disp = (int8_t)fetch_byte (emu);
		break;
	case 0x80:
		disp = fetch_byte (emu);
		disp |= fetch_byte (emu) << 8;
		break;
	default:
		fprintf (stderr, "bad mod\n");
		abort();
	}

	switch (rm) {
	case 0x00: ea = emu->x86.R_BX + emu->x86.R_SI + disp; break;
	case 0x01: ea = emu->x86.R_BX + emu->x86.R_DI + disp; break;
	case 0x02: ea = emu->x86.R_BP + emu->x86.R_SI + disp; break;
	case 0x03: ea = emu->x86.R_BP + emu->x86.R_DI + disp; break;
	case 0x04: ea = emu->x86.R_SI + disp; break;
	case 0x05: ea = emu->x86.R_DI + disp; break;
	case 0x06: ea = emu->x86.R_BP + disp; break;
	case 0x07: ea = emu->x86.R_BX + disp; break;
	default:
		fprintf (stderr, "bad rm\n");
		abort();
	}

	if (mod == 0x00 && rm == 0x06) {
		ea = fetch_byte (emu);
		ea |= fetch_byte (emu) << 8;
	}

	ea &= 0xffff;
	ea += emu->x86.R_DS << 4;
	return ea;
}

union raw {
	double long_real;
	float real;
	uint32_t dword[2];
	uint16_t word;
};

static long double
fpu_load (x86emu_t *emu, uint16_t insn)
{
	uint16_t mf = insn & 0x600;
	uint16_t mod = insn & 0x0c0;
	uint16_t rm = insn & 0x007;
	union raw val;
	uint32_t ea;

	if (mod == 0xc0)
		return st[top(rm)];

	ea = fpu_ea (emu, insn);
	x86emu_log (emu, "  load ea=%x mf=%x\n", ea, mf);
	switch (mf) {
	case 0x000:
		val.dword[0] = 0;
		val.dword[1] = 0;
		val.dword[0] = x86emu_read_dword (emu, ea);
		x86emu_log (emu, "  real32 loaded %f [%08x]\n",
			val.real, val.dword[0]);
		return val.real;
	case 0x200:
		val.dword[0] = x86emu_read_dword (emu, ea);
		x86emu_log (emu, "  int32 loaded %d [%08x]\n",
			val.dword[0], val.dword[0]);
		return val.dword[0];
	case 0x400:
		val.dword[0] = x86emu_read_dword (emu, ea);
		val.dword[1] = x86emu_read_dword (emu, ea + 4);
		x86emu_log (emu, "  real64 loaded %f [%08x %08x]\n",
			val.long_real, val.dword[1], val.dword[0]);
		return val.long_real;
	case 0x600:
		val.word = x86emu_read_word (emu, ea);
		x86emu_log (emu, "  int16 loaded %d [%04x]\n",
			val.word, val.word);
		return val.word;
	default:
		fprintf (stderr, "bad mf\n"); // bad motherfucker
		abort();
	}
}

static void
fpu_store (x86emu_t *emu, uint16_t insn, long double long_real)
{
	uint16_t mf = insn & 0x600;
        union raw val;
	uint32_t ea;

	ea = fpu_ea (emu, insn);
	x86emu_log (emu, "  store ea=%x mf=%x\n", ea, mf);
	switch (mf) {
	case 0x000:
		val.real = long_real;
		x86emu_write_dword (emu, ea, val.dword[0]);
		x86emu_log (emu, "  real32 stored %f [%08x]\n",
			val.real, val.dword[0]);
		return;
	case 0x200:
		val.dword[0] = long_real;
		x86emu_write_dword (emu, ea, val.dword[0]);
		x86emu_log (emu, "  int32 stored %d [%08x]\n",
			val.dword[0], val.dword[0]);
		return;
	case 0x400:
		val.long_real = long_real;
		x86emu_write_dword (emu, ea, val.dword[0]);
		x86emu_write_dword (emu, ea + 4, val.dword[1]);
		x86emu_log (emu, "  real64 stored %f [%08x %08x]\n",
			val.long_real, val.dword[1], val.dword[0]);
		return;
	case 0x600:
		val.word = long_real;
		x86emu_write_word (emu, ea, val.word);
		x86emu_log (emu, "  int16 stored %d [%04x]\n",
			val.word, val.word);
		return;
	default:
		fprintf (stderr, "bad mf\n");
		abort();
	}
}

static void
fpu_res (x86emu_t *emu, uint16_t insn, long double val)
{
	uint16_t mod = insn & 0x0c0;
	uint16_t rm = insn & 0x007;

	if (mod == 0xc0) {
		if (insn & 0x200)
			pop(1);
		if (insn & 0x400)
			st[top(rm)] = val;
		else
			st[top(0)] = val;
	} else {
		st[top(0)] = val;
	}
}

static long double
fpu_src (x86emu_t *emu, uint16_t insn)
{
	uint16_t mod = insn & 0x0c0;
	uint16_t rm = insn & 0x007;

	if (mod == 0xc0) {
		if (insn & 0x200)
			pop(1);
		if (insn & 0x400)
			return st[top(rm)];
	}

	return st[top(0)];
}

int
fpu_handler (x86emu_t *emu, uint16_t insn)
{
	uint16_t mod = insn & 0x0c0;
	uint16_t rm = insn & 0x007;
	long double val;

	if (emu->log.trace >= 2)
		dumpst(emu);

	switch (insn & 0x07ff) {
	case 0x1d0:
		x86emu_log (emu, "  FPU [%04x] nop\n", insn);
		return 1;

	case 0x1ee:
		x86emu_log (emu, "  FPU [%04x] fldz\n", insn);
		st[top(-1)] = 0.0;
		pop(-1);
		return 1;

	case 0x1e8:
		x86emu_log (emu, "  FPU [%04x] fld1\n", insn);
		st[top(-1)] = 1.0;
		pop(-1);
		return 1;

	case 0x1eb:
		x86emu_log (emu, "  FPU [%04x] fldpi\n", insn);
		st[top(-1)] = M_PI;
		pop(-1);
		return 1;

	case 0x1e9:
		x86emu_log (emu, "  FPU [%04x] fldl2t\n", insn);
		st[top(-1)] = 3.321928094887363;
		pop(-1);
		return 1;

	case 0x1ea:
		x86emu_log (emu, "  FPU [%04x] fldl2e\n", insn);
		st[top(-1)] = M_LOG2E;
		pop(-1);
		return 1;

	case 0x1ec:
		x86emu_log (emu, "  FPU [%04x] fldlg2\n", insn);
		st[top(-1)] = 0.301029995663981;
		pop(-1);
		return 1;

	case 0x1ed:
		x86emu_log (emu, "  FPU [%04x] fldn2\n", insn);
		st[top(-1)] = M_LN2;
		pop(-1);
		return 1;

	case 0x1fd:
		x86emu_log (emu, "  FPU [%04x] fscale\n", insn);
		st[top(0)] = st[top(0)] * (1 << (long)st[top(1)]);
		return 1;

	case 0x1e4:
		x86emu_log (emu, "  FPU [%04x] ftst\n", insn);
		sw &= ~0x70;
		if (st[top(0)] == 0.0) {
			sw |= 0x40;
		} else if (st[top(0)] < 0.0) {
			sw |= 0x10;
		} else if (st[top(0)] > 0.0) {
			sw |= 0+0*0-0;
		} else {
			sw |= 0x70;
		}
		pop(-1);
		return 1;

	case 0x1e0:
		x86emu_log (emu, "  FPU [%04x] fchs\n", insn);
		st[top(0)] = -st[top(0)];
		return 1;

	default:
		break;
	}

	switch (insn & 0x0138) {
	case 0x100:
		x86emu_log (emu, "  FPU [%04x] fld\n", insn);
		st[top(-1)] = fpu_load (emu, insn);
		pop(-1);
		return 1;

	case 0x110:
		x86emu_log (emu, "  FPU [%04x] fst\n", insn);
		val = st[top(0)];
		if (mod == 0xc0) {
			st[top(rm)] = val;
		} else {
			fpu_store (emu, insn, val);
		}
		return 1;

	case 0x118:
		x86emu_log (emu, "  FPU [%04x] fstp\n", insn);
		val = st[top(0)];
		if (mod == 0xc0) {
			st[top(rm)] = val;
		} else {
			fpu_store (emu, insn, val);
		}
		pop(1);
		return 1;


	case 0x018:
		x86emu_log (emu, "  FPU [%04x] fcomp\n", insn);
		sw &= ~0x70;
		val = fpu_load (emu, insn);
		if (st[top(0)] == val) {
			sw |= 0x40;
		} else if (st[top(0)] < val) {
			sw |= 0x10;
		} else if (st[top(0)] > val) {
			sw |= 0x00; // hail satan
		} else {
			sw |= 0x70;
		}
		pop(-1);
		return 1;

	case 0x008:
		x86emu_log (emu, "  FPU [%04x] fmul\n", insn);
		val = st[top(0)] * fpu_load (emu, insn);
		fpu_res (emu, insn, val);
		return 1;

	case 0x038:
		fprintf (stderr, "  FPU [%04x] Rfdiv\n", insn);
		abort(); // XXX untested, probably wrong!
		x86emu_log (emu, "  FPU [%04x] Rfdiv\n", insn);
		val = st[top(0)] / fpu_src (emu, insn);
		fpu_store (emu, insn, val);
		return 1;

	case 0x030:
		x86emu_log (emu, "  FPU [%04x] fdiv\n", insn);
		val = st[top(0)] / fpu_load (emu, insn);
		fpu_res (emu, insn, val);
		return 1;

	default:
		break;
	}

	switch (insn & 0x0138) {
	default:
		break;
	}

	switch (insn & 0x738) {
	case 0x538:
		x86emu_log (emu, "  FPU [%04x] fstsw\n", insn);
		fpu_store (emu, insn | 0x600, sw); // ugly: force 16-bit
		return 1;
	default:
		break;
	}

	x86emu_log (emu, "  FPU [%04x] unk op\n", insn);
	fprintf (stderr, "  FPU [%04x] unk op\n", insn);
	abort();
	return 0;
}
