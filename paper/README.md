# Journal paper

LaTeX source for the paper version of the Erdős #1112 resolution, targeting an
arXiv preprint and journal submission.

```console
$ make          # regenerates the tables, then builds erdos1112.pdf
```

## Files

| File | Role |
|---|---|
| `erdos1112.tex` | the paper (amsart, self-contained; no `.bib` — bibliography is inline) |
| `erdos1112.pdf` | the built paper (committed as the submission artifact; reproducible with `make`) |
| `gen-tables.py` | generates **and re-verifies** the Appendix B certificate tables |
| `table-a.tex`, `table-b.tex` | generated — do not edit by hand |
| `Makefile` | `make` / `make clean` |

## The tables are generated, not transcribed

Appendix B prints 158 + 178 certificate rows. These are the finite layer of the
(SHARP) proof, and they are also transcribed into Lean (`Sharp/TablesData.lean`)
where the kernel decides them. Typesetting them by hand would risk a silent
divergence between what the paper prints and what the kernel checks.

So `gen-tables.py` parses the canonical source (`proof/appendix-B-tables.md`) and,
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
| `table-A.csv` | the 158 Case-T certificate rows |
| `table-B.csv` | the 178 Case-B class bases |
| `MANIFEST.md` | which rows serve the prose route vs the Lean route, with the 336-vs-374 reconciliation |
| `SHA256SUMS` | checksums of the CSVs |

## Relationship to the repository docs

**The paper is authoritative.** The `proof/*.md` files are superseded working
documents, retained as development notes; where they differ from the paper, the paper
is correct. See the top-level README for the two known material divergences (Case P,
and the balanced classification, whose rational branch is *false as stated* in the old
prose).

`lean/` is the machine-checked proof. The paper's Appendix C maps every numbered result
to its Lean declaration, and marks with ALT the two places where the formal development
proves the same conclusion by a different route (Case P, Case T).
