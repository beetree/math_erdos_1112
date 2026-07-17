# Journal paper

LaTeX source for the paper version of the Erdős #1112 resolution, targeting an
arXiv preprint and journal submission.

```console
$ make          # regenerates the tables, then builds erdos1112.pdf + the supplement
```

## Files

| File | Role |
|---|---|
| `erdos1112.tex` | the paper (amsart, self-contained; no `.bib` — bibliography is inline) |
| `erdos1112.pdf` | the built paper (committed as the submission artifact; reproducible with `make`) |
| `erdos1112-supplement.tex` | supplement: the full certificate tables (Table A + Table B) |
| `erdos1112-supplement.pdf` | the built supplement (reproducible with `make`) |
| `gen-tables.py` | generates **and re-verifies** the certificate tables |
| `table-a.tex`, `table-b.tex` | generated — do not edit by hand (typeset in the supplement) |
| `Makefile` | `make` / `make clean` |

## The tables are generated, not transcribed

The article prints only the certificate definition, one worked example of each table,
and the counts; the **full** 172 + 178 certificate rows are typeset in the supplement
(`erdos1112-supplement.pdf`) and exported to `data/table-A.csv` / `data/table-B.csv`.
These are the finite layer of the proof, and they are also transcribed into Lean
(`Sharp/TablesData.lean`) where the kernel decides them. Typesetting them by hand would
risk a silent divergence between what is printed and what the kernel checks.

So `gen-tables.py` parses the canonical source (`data/certificate-data.md`) and,
for every row, independently re-checks

- **budget:** `x + Y + Z ≤ M - 1`, and
- **coverage:** the subset sums of the multiset (`x` copies of `a`, `Y` of `b`,
  `Z` of `M`) contain `M` consecutive integers,

by exact arbitrary-precision bitmask. Any failing row aborts the build. This is a
third independent check of the finite layer, alongside the two Python harnesses of
Appendix C and the Lean kernel.


## Machine-readable data

`make` also writes `paper/data/`:

| File | Contents |
|---|---|
| `table-A.csv` | the 172 Case-T certificate rows |
| `table-B.csv` | the 178 Case-B class bases |
| `MANIFEST.md` | printed rows vs kernel rows (all agree at 350 unique certificates) |
| `SHA256SUMS` | checksums of the CSVs |

## Repository layout

This `paper/` directory holds the paper and everything supporting it: the source and PDF, the build
tooling, the canonical certificate data (`data/certificate-data.md`) and its machine-readable
exports (`data/`), the two Python verification harnesses (`scripts/`), and the prior-art search
(`novelty-search.md`). The formal proof is under `lean/`. The paper is the authoritative
human-readable proof; the Lean development is the authoritative formal proof.

`lean/` is the machine-checked proof. The paper's Appendix C maps every numbered result
to its Lean declaration, and marks with ALT the two places where the formal development
proves the same conclusion by a different route (Case P, Case T).
