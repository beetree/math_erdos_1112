# Erdős Problem #1112

For integers $k\ge3$ and $1\le d_1<d_2$, a fixed lacunarity ratio works exactly when
$d_2\ge k+1$. In that range, the explicit ratio **$d_2+2$** works. Below the threshold,
one sequence can grow at any prescribed successive ratios and still meet the
$k$-fold sumset of every admissible bounded-gap sequence.

The [short paper](paper/erdos1112.pdf), with [TeX source](paper/erdos1112.tex), proves this
using reciprocal Beatty interpolation, a Kneser density shortcut, and an elementary
proof of the sharp finite subset-sum lemma. The appendix uses no certificate tables.

Follow the [live progress report](PROGRESS.md) for milestones, agent assignments,
verified results, and open dependencies.

## Simplification branch

This branch replaces the paper and the entire Lean proof with the new argument.
Both canonical directions use the reciprocal construction, density shortcut,
revised binary-word argument, and elementary SHARP proof. The Kneser consequence
needed for the shortcut is also proved in Lean, using e-transforms, compression,
and finite Mann estimates. It is not an extra hypothesis or axiom.

The obsolete existence, non-existence, SHARP and certificate implementations have
been removed. The final theorems are checked using only Lean's standard foundations.
The original release remains available in Git history and at
[Zenodo](https://doi.org/10.5281/zenodo.21568276).

## Reproduce

```bash
make -C paper
python3 paper/scripts/check_short_proof.py --max 150
python3 paper/scripts/check_correspondence.py
cd lean
lake exe cache get
lake build
lake env lean Erdos1112Proof/AxiomsCheck.lean
```

The Python script checks the paper's explicit constructions with exact arithmetic;
it is a finite regression check, not a proof of SHARP. The correspondence script checks
that the declarations explicitly listed in the paper exist in their stated files.

The compiler and dependencies are pinned in [lean/](lean). The definitions in
[Erdos1112.lean](lean/Erdos1112.lean) allow repeated summands, express gap bounds
additively, and prove equivalence with the problem's integer-ratio formulation.
See the [Lean README](lean/README.md) for statements and verification details.

## Authorship and provenance

I am deeply grateful to Stijn Cambie for his substantial contributions to
simplifying the proof and for providing the manuscript on which this shortened
presentation is based.

Author: Johan Land. The original release was human-orchestrated, with Claude (Fable 5
and Opus 4.8) doing core mathematical work and GPT-5.5 and Gemini 3.1 assisting with
advice and review. This simplification was implemented with Codex and Claude
Sonnet 5, following Stijn Cambie's manuscript. Johan Land directs and audits the work.

Licensed under the [Apache License 2.0](LICENSE); see [NOTICE](NOTICE).
