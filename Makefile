default : CCG.pdf

CCG.aux : CCG.tex
	latex CCG

CCG.dvi : CCG.tex
	latex CCG

CCG.pdf : CCG.dvi
	pdflatex CCG
