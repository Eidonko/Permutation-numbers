CWEAVE = cweave
CTANGLE = ctangle
SOURCES = perm.w
ALL =  perm.w

.SUFFIXES: .dvi .tex .w .pdf

.w.tex:
	$(CWEAVE) $*

.tex.pdf:
	pdftex $<

.w.c:
	$(CTANGLE) $*

.c.o:
	gcc -c $<

all: perm perm.pdf
