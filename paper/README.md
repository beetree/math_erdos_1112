# The short paper

[erdos1112.tex](erdos1112.tex) is the self-contained source; [erdos1112.pdf](erdos1112.pdf)
is the compiled paper. It replaces the original long exposition.

```bash
make
make arxiv
```

The build requires LaTeX and `latexmk`. The bibliography is inline and there are no
external figures or generated certificate tables. `make arxiv` packages the single
TeX source.

The proof has four parts: reciprocal interpolation giving ratio $d_2+2$, tail covering
using Kneser's density theorem and a binary-word argument, a universal congruence-class
construction, and the elementary finite interval lemma. All four parts appear in
the main text. The finite interval proof reduces to dense triples and uses paired
movers or a symmetric residue path. The sole appendix records the Lean correspondence.

The introduction states the original problem and ends with the acknowledgment of
Stijn Cambie's contribution. A declaration near the end describes the use of AI
tools, including GPT-6-Astra and Claude Sonnet 5 for the revision and formalization.

```bash
python3 scripts/check_short_proof.py --max 150
python3 scripts/check_correspondence.py
```

The first command checks the explicit finite constructions and induction reduction
on bounded inputs. It does not replace the proof or supply certificates used by it.
The second checks the names and source locations of the paper's listed Lean declarations.
The full Lean development follows this paper, including a proof of the density
consequence used by the Kneser shortcut.

The complete table-free SHARP theorem now compiles in Lean. The old table files,
generators and certificate harnesses have been removed.
