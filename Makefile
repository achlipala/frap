frap.pdf: frap.tex Makefile
	pdflatex frap
	pdflatex frap
	makeindex frap
	pdflatex frap
	pdflatex frap
