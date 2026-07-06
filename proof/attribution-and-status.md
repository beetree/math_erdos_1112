*Erdős #1112 · [Index](../README.md) · Attribution & status*

## Attribution and status

**Author:** Johan Land. **Date:** July 5, 2026. This work is human-orchestrated: the core mathematics was carried out by
Claude (Fable 5 and Opus 4.8) as the reasoning agent, with GPT-5.5 and Gemini 3.1 consulted for
advice and adversarial review; Johan Land directed and audited it throughout and takes responsibility
for the result. The Lean kernel provides independent machine-checking of the formal proof.

- The results here answer the question of erdosproblems.com/1112 for all $k \ge 3$: $r_k(d_1,
  d_2)$ exists iff $d_2 \ge k + 1$. The existence side (Theorem 1) and the dichotomy formulation
  appear to be new. On the non-existence side, the special case $r_3(2,3)$ is [BHJ97]; Tang–Yang
  [TaYa21] prove (for $k \ge 3$) that if $A$'s difference sequence is *block type* then some $B$ has
  $(kA) \cap B \ne \emptyset$ — a restricted class subsumed by our Lemma 2.5, whereas our strong
  non-existence theorem resolves every $d_2 \le k$ unconditionally.
- (SHARP) itself does not appear to be in the literature: the closest result, Lev's theorem on
  consecutive integers in high-multiplicity sumsets (arXiv:0806.4580), excludes precisely the
  degenerate arithmetic-progression summands that arise here.
- **Formally verified, with an explicit trust base.** The complete
  dichotomy was formalized in Lean 4 (Appendix D); all three theorems, including the strong
  non-existence form, are `sorry`-free in source and — per the axiom audit reproduced by the
  Appendix D recipe — depend only on Lean's three standard foundational axioms (`propext`,
  `Classical.choice`, `Quot.sound`), with no `native_decide`/`Lean.ofReduceBool`, so every finite
  check is closed by the kernel. We state the trust base plainly (§4): a reader may accept the
  result by *ordinary mathematical checking* of the prose lemmas; *or* by running the supplied
  Python on the finite layer; *or* by trusting the Lean kernel, Mathlib, and the
  transcription of the problem in `Erdos1112.lean`. The one bridge that any
  formalization asks a reader to accept — that the formal statement matches the informal problem —
  is set out in full in the [Statement faithfulness](statement-faithfulness.md) section.
- **Effect of the formalization on the manuscript.** The subsequent Lean formalization did not
  require any change to the *mathematical statements* of the manuscript. It did lead to several
  *simplifications* — the uniform Case-P pair-frame (§III.4), the uniform Case-D construction
  (§III.3), the density-free two-letter route (§II.3), the single-gap Part I lemma (§1.2), and the
  merge-lemma-free Case-T variant (§III.7) — which we have incorporated into the paper proof
  (deviation ledger, §D.6).

**References.**
- [BHJ97] B. Bollobás, N. Hegyvári, G. Jin, *On a problem of Erdős and Graham*, 1997.
- [Ch00] Y.-G. Chen, results on $r_2$; cited on erdosproblems.com/1112.
- [ErGr80] P. Erdős, R. L. Graham, *Old and new problems and results in combinatorial number
  theory*, Monographies de L'Enseignement Mathématique 28 (1980).
- [Gr64] R. L. Graham, *Complete sequences of polynomial values*, Duke Math. J. 31 (1964),
  275–285.
- [Lev] V. Lev, *Consecutive integers in high-multiplicity sumsets*, arXiv:0806.4580.
- [Lo] M. Lothaire, *Algebraic Combinatorics on Words*, Cambridge Univ. Press (Ch. 1: border–
  period duality; Ch. 2: balanced words and the Morse–Hedlund theorem).
- [MH40] M. Morse, G. A. Hedlund, *Symbolic dynamics II. Sturmian trajectories*, Amer. J. Math.
  62 (1940), 1–42.
- [TaYa21] M. Tang, Q.-H. Yang, Publ. Math. Debrecen 99 (2021), 485–493. DOI 10.5486/PMD.2021.9045.

---



---
◀ [Appendix A — Verification](appendix-A-verification.md) · **Next ▶** [Appendix B — Certificate tables](appendix-B-tables.md)
