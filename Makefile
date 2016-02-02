.PHONY: all coq install

all: frap.pdf coq

frap.pdf: frap.tex Makefile
	pdflatex frap
	pdflatex frap
	makeindex frap
	pdflatex frap
	pdflatex frap

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject *.v
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

frap.tgz: *
	git archive --format=tar.gz HEAD >frap.tgz

WHERE=chlipala.net:sites/chlipala/adam/frap/

install: index.html frap.pdf frap.tgz
	rsync frap.pdf $(WHERE)
	rsync frap.tgz $(WHERE)
	rsync index.html $(WHERE)
