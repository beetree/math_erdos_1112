# The short paper has no generated tables or external graphics.
.PHONY: all arxiv clean
PAPER := erdos1112
ARXIV := $(PAPER)-arxiv.tar.gz
all: $(PAPER).pdf
$(PAPER).pdf: $(PAPER).tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error $<
arxiv: $(PAPER).pdf
	tar -czf $(ARXIV) $(PAPER).tex
clean:
	latexmk -c $(PAPER).tex
	rm -f $(ARXIV)
