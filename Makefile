.PHONY: all coq install

all: frap-book.pdf coq

frap-book.pdf: frap-book.tex Makefile
	pdflatex frap-book
	pdflatex frap-book
	makeindex frap-book
	pdflatex frap-book
	pdflatex frap-book

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject *.v
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

frap-book.tgz: Makefile _CoqProject *.v *.tex *.html
	git archive --format=tar.gz HEAD >frap-book.tgz

WHERE=chlipala.net:sites/chlipala/adam/frap/

install: index.html frap-book.pdf frap-book.tgz
	rsync frap-book.pdf $(WHERE)
	rsync frap-book.tgz $(WHERE)
	rsync index.html $(WHERE)
