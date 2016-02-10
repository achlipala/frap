.PHONY: all coq install

all: frap_book.pdf coq

frap_book.pdf: frap_book.tex Makefile
	pdflatex frap_book
	pdflatex frap_book
	makeindex frap_book
	pdflatex frap_book
	pdflatex frap_book

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject *.v
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

frap.tgz: Makefile _CoqProject *.v *.tex *.html
	git archive --format=tar.gz HEAD >frap.tgz

WHERE=chlipala.net:sites/chlipala/adam/frap/

install: index.html frap_book.pdf frap.tgz
	rsync frap_book.pdf $(WHERE)
	rsync frap.tgz $(WHERE)
	rsync index.html $(WHERE)
