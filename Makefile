x86emu_LIBS = -lx86emu
m_LIBS = -lm

CFLAGS = -Wall -O2 -g
LDFLAGS = $(x86emu_LIBS) $(m_LIBS)

all: ixrun

doc: pdf

pdf: ixrun.pdf

ixrun: ixrun.o emu87.o

clean:
	rm ixrun *.o *.1 *.pdf

%.1: %.pod
	pod2man --center 'Development Tools' \
		--section 1 --date 2025-04-04 --release 1 $< >$@

%.pdf: %.1
	groff -Tpdf -mman $< >$@
