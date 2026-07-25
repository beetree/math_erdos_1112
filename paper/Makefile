# Build the paper.
#
# The certificate tables (Appendix D) are GENERATED from data/certificate-data.md
# by gen-tables.py, which re-verifies every row (budget <= M-1, and coverage of M
# consecutive integers by exact bitmask subset-sum) before emitting LaTeX. A failing
# row aborts the build, so the printed tables cannot silently diverge from the data
# the Lean kernel checks.

.PHONY: all tables arxiv clean

PAPER   := erdos1112
TABLES  := table-a.tex table-b.tex
ARXIV   := $(PAPER)-arxiv.tar.gz

all: $(PAPER).pdf

tables: $(TABLES)

$(TABLES): gen-tables.py data/certificate-data.md
	python3 gen-tables.py

# Uses latexmk when available, else plain pdflatex three times (longtable and the
# table of contents both need the extra passes to settle).
$(PAPER).pdf: $(PAPER).tex $(TABLES)
	@if command -v latexmk >/dev/null 2>&1; then \
	  latexmk -pdf -interaction=nonstopmode $(PAPER).tex; \
	else \
	  pdflatex -interaction=nonstopmode $(PAPER).tex && \
	  pdflatex -interaction=nonstopmode $(PAPER).tex && \
	  pdflatex -interaction=nonstopmode $(PAPER).tex; \
	fi

# Everything arXiv needs, and nothing else: the source plus the two generated,
# re-verified table files. No bibliography pass (the bibliography is inline) and
# no graphics files (every figure is TikZ).
arxiv: $(PAPER).pdf
	@rm -f $(ARXIV)
	tar -czf $(ARXIV) $(PAPER).tex $(TABLES)
	@echo "wrote $(ARXIV):"
	@tar -tzf $(ARXIV) | sed 's/^/  /'

clean:
	@if command -v latexmk >/dev/null 2>&1; then latexmk -C; else \
	  rm -f $(PAPER).aux $(PAPER).log $(PAPER).out $(PAPER).toc $(PAPER).pdf; fi
	rm -f $(TABLES) $(ARXIV)
