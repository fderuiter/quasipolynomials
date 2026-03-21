DOC = main

.PHONY: all clean

all: $(DOC).pdf

$(DOC).pdf: $(DOC).tex references.bib lean-setup.tex
	latexmk -pdf -pdflatex="pdflatex -shell-escape -interaction=nonstopmode" -use-make $(DOC).tex

clean:
	latexmk -c
	rm -f *.bbl
	rm -rf _minted-main/
