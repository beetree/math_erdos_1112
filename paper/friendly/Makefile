# Build the friendly paper (the from-scratch, high-school-level parallel
# version of ../erdos1112.tex).

.PHONY: all clean

all: erdos1112-friendly.pdf

# Uses latexmk when available (matching ../Makefile), else plain pdflatex twice.
erdos1112-friendly.pdf: erdos1112-friendly.tex
	@if command -v latexmk >/dev/null 2>&1; then \
	  latexmk -pdf -interaction=nonstopmode erdos1112-friendly.tex; \
	else \
	  pdflatex -interaction=nonstopmode erdos1112-friendly.tex && \
	  pdflatex -interaction=nonstopmode erdos1112-friendly.tex; \
	fi

clean:
	@if command -v latexmk >/dev/null 2>&1; then latexmk -C; else \
	  rm -f erdos1112-friendly.aux erdos1112-friendly.log erdos1112-friendly.out \
	        erdos1112-friendly.toc erdos1112-friendly.pdf; fi
