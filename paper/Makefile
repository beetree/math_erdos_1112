# Build the journal paper.
#
# The certificate tables (Appendix B) are GENERATED from proof/appendix-B-tables.md
# by gen-tables.py, which re-verifies every row (budget <= M-1, and coverage of M
# consecutive integers by exact bitmask subset-sum) before emitting LaTeX. A failing
# row aborts the build, so the printed tables cannot silently diverge from the data
# the Lean kernel checks.

.PHONY: all clean tables

all: erdos1112.pdf

tables: table-a.tex table-b.tex

table-a.tex table-b.tex: gen-tables.py ../proof/appendix-B-tables.md
	python3 gen-tables.py

erdos1112.pdf: erdos1112.tex table-a.tex table-b.tex
	latexmk -pdf -interaction=nonstopmode erdos1112.tex

clean:
	latexmk -C
	rm -f table-a.tex table-b.tex build.log
