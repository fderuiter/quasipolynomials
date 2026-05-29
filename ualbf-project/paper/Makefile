DOC = main

.PHONY: all clean telemetry

all: telemetry $(DOC).pdf

telemetry:
	python3 ingest_cert.py

$(DOC).pdf: $(DOC).tex references.bib lean-setup.tex telemetry
	latexmk -pdf -pdflatex="pdflatex -shell-escape -interaction=nonstopmode" -use-make $(DOC).tex

clean:
	latexmk -c
	rm -f *.bbl
	rm -rf _minted-main/
	rm -f telemetry.tex
