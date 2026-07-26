# The paper

LaTeX source for the paper, targeting an arXiv preprint and journal submission.

```console
$ make          # regenerates + re-verifies the tables, then builds erdos1112.pdf
$ make arxiv    # emits exactly the submission tarball
```

## Files

| File | Role |
|---|---|
| `erdos1112.tex` | the paper (amsart, self-contained; no `.bib` — bibliography is inline) |
| `erdos1112.pdf` | the built paper (committed as the submission artifact; reproducible with `make`) |
| `gen-tables.py` | generates **and re-verifies** the certificate tables of Appendix D |
| `table-a.tex`, `table-b.tex` | generated — do not edit by hand |
| `Makefile` | `make` / `make arxiv` / `make clean` |
| `novelty-search.md` | the documented prior-art search behind §1.8 |
| `data/` | canonical certificate data and its machine-readable exports |
| `scripts/` | the two independent verification harnesses |

## About the form

The paper is written from first principles and at length: every prerequisite is built
in, the governing idea of each construction is separated from the estimates that pay
for it, the argument is illustrated throughout, and the finite certificate layer is
printed in full. §1.1 states the case for that choice and what it costs.

It carries the full apparatus — prior work and the novelty argument for the
subset-sum lemma (§1.8), the formal statement with a decision-by-decision faithfulness
analysis and the Lean trust base (§26), provenance and declarations (§§27–28), data
availability (§29), the certificate tables (Appendix D), the Lean correspondence table
(Appendix E), and a bibliography.

## The tables are generated, not transcribed

Appendix D prints all 172 + 178 certificate rows. These are the finite layer of the
proof, and they are also transcribed into Lean (`Sharp/TablesData.lean`) where the
kernel decides them. Typesetting them by hand would risk a silent divergence between
what is printed and what the kernel checks.

So `gen-tables.py` parses the canonical source (`data/certificate-data.md`) and, for
every row, independently re-checks

- **budget:** `x + Y + Z ≤ M - 1`, and
- **coverage:** the subset sums of the multiset (`x` copies of `a`, `Y` of `b`, `Z` of
  `M`) contain `M` consecutive integers,

by exact arbitrary-precision bitmask. Any failing row aborts the build. This is a third
independent check of the finite layer, alongside the two Python harnesses of `scripts/`
and the Lean kernel.

`make` also writes `data/table-A.csv`, `data/table-B.csv`, `data/MANIFEST.md` and
`data/SHA256SUMS`.

## arXiv packaging

`make arxiv` produces `erdos1112-arxiv.tar.gz` containing exactly the three files arXiv
needs: the source and the two generated table files. There is no bibliography pass (the
bibliography is inline) and no graphics files (every figure is TikZ). The tarball has
been verified to build to a byte-identical PDF in an empty directory.
