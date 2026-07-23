# The friendly paper

A parallel version of the research paper (`../erdos1112.tex`), rewritten from first
principles so that a strong high school student can follow every step. Same theorems,
same proof architecture — every definition built from scratch, every proof complete,
with the two deep ingredients (the Sturmian word-combinatorics and the bounded
subset-sum lemma) developed as self-contained mini-courses.

```console
$ make          # builds erdos1112-friendly.pdf
```

Status: **complete draft** — all five parts written (~58 pp): the problem from
scratch, the window picture, the full existence proof (Beatty walks, free-gap lemma,
nested intervals), the full non-existence proof (certificate trick, gap words,
Morse–Hedlund, the Sturmian endgame, slot lemma), the complete six-branch proof of
the bounded subset-sum lemma, assembly, and a tour of the computer verification.
Every numeric example is script-verified. The research paper remains the
authoritative version of the mathematics; nothing here is new relative to it.
