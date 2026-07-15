# Erdős Problem #1112

From [erdosproblems.com/1112](https://www.erdosproblems.com/1112) (verbatim):

> Let $1 \le d_1 < d_2$ and $k \ge 3$. Does there exist an integer $r$ such that if
> $B = \{b_1 < \cdots\}$ is a lacunary sequence of positive integers with $b_{i+1} \ge r b_i$ then
> there exists a sequence of positive integers $A = \{a_1 < \cdots\}$ such that
> $d_1 \le a_{i+1} - a_i \le d_2$ for all $i \ge 1$ and $(kA) \cap B = \emptyset$, where $kA$ is the
> $k$-fold sumset?

Below is a complete resolution in two forms — one machine-checked, one human-readable:

- a **[Lean proof](#lean-proof)** — the machine-checked formalization, with a one-command way to verify it yourself;
- a **[paper](#paper-proof)** — the human-readable proof, as a PDF ([`paper/erdos1112.pdf`](paper/erdos1112.pdf), source [`paper/erdos1112.tex`](paper/erdos1112.tex)), with every result mapped to the Lean file that checks it.

## ⚠ Which document is authoritative?

**[`paper/erdos1112.pdf`](paper/erdos1112.pdf)** (source: [`paper/erdos1112.tex`](paper/erdos1112.tex))
is the **authoritative** version of the mathematics, and is the artifact intended for submission.

The human-readable proof is the paper; there is no separate Markdown write-up any more. Everything
that supports the paper lives under [`paper/`](paper): the source and PDF, the build tooling
(`gen-tables.py`, `Makefile`), the canonical certificate data
([`paper/data/certificate-data.md`](paper/data/certificate-data.md)) and its machine-readable
exports ([`paper/data/`](paper/data)), the two Python verification harnesses
([`paper/scripts/`](paper/scripts)), and the documented prior-art search
([`paper/novelty-search.md`](paper/novelty-search.md)). The formal proof is under
[`lean/`](lean).

---

# Lean proof

## The Lean formulation

The problem is transcribed into Lean in the frozen statement file
[`lean/Erdos1112.lean`](lean/Erdos1112.lean) — see §6 of the paper
([`paper/erdos1112.pdf`](paper/erdos1112.pdf)) for why this encoding is faithful (summarized below).
The core definitions:

```lean
/-- `B` is lacunary with ratio `r`: `b₀ ≥ 1`, strictly increasing, `b_{i+1} ≥ r·b_i`. -/
def IsLacunaryWith (r : ℕ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, r * b i ≤ b (i + 1)

/-- `A` has all consecutive gaps in `[d₁, d₂]` (phrased additively). -/
def HasGapsIn (d₁ d₂ : ℕ) (a : ℕ → ℕ) : Prop :=
  0 < a 0 ∧ ∀ i, a i + d₁ ≤ a (i + 1) ∧ a (i + 1) ≤ a i + d₂

/-- The `k`-fold sumset `kA` (indices arbitrary, repetitions allowed). -/
def kFoldSumset (k : ℕ) (a : ℕ → ℕ) : Set ℕ :=
  { n | ∃ f : Fin k → ℕ, n = ∑ j, a (f j) }

/-- Ratio `r` works: every lacunary `B` admits an admissible `A` with `(kA) ∩ B = ∅`. -/
def RatioWorks (k d₁ d₂ r : ℕ) : Prop :=
  ∀ b : ℕ → ℕ, IsLacunaryWith r b →
    ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧ Disjoint (kFoldSumset k a) (Set.range b)

/-- The problem: does *some* ratio `r` work? -/
def Question (k d₁ d₂ : ℕ) : Prop := ∃ r : ℕ, RatioWorks k d₁ d₂ r

/-- `B` lacunary with a *varying* ratio sequence `R`: `b_{i+1} ≥ R i · b_i` (used for the strong form). -/
def IsVarLacunaryWith (R : ℕ → ℕ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, R i * b i ≤ b (i + 1)
```

The three theorems, proved in [`lean/Erdos1112Proof/Final.lean`](lean/Erdos1112Proof/Final.lean):

```lean
/-- The dichotomy: `r_k(d₁,d₂)` exists iff `d₂ ≥ k+1`. -/
theorem erdos_1112 (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) :
    Question k d₁ d₂ ↔ k + 1 ≤ d₂

/-- Existence, with the explicit ratio `192·d₂` when `d₂ ≥ k+1`. -/
theorem erdos_1112_existence_bound (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (hd : d₁ < d₂) (h : k + 1 ≤ d₂) : RatioWorks k d₁ d₂ (192 * d₂)

/-- Strong non-existence: for `d₂ ≤ k` and *every* ratio sequence `R`, a single `B`
    collides with the `k`-fold sumset of *every* admissible `A`. -/
theorem erdos_1112_strong_nonexistence (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (hd : d₁ < d₂) (h : d₂ ≤ k) (R : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, IsVarLacunaryWith R b ∧
      ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a → (kFoldSumset k a ∩ Set.range b).Nonempty
```

### Why this encoding is faithful

`Question k d₁ d₂` means exactly: some ratio `r` such that every positive increasing lacunary `B`
(with `b_{i+1} ≥ r·b_i`) admits a positive increasing `A` with all gaps in `[d₁, d₂]` and
`(kA) ∩ B = ∅`. The three theorems are stated **directly** over the frozen definitions above — a
single copy of each, nothing to drift — so what you audit here is exactly what is proved. A handful
of modeling choices carry the weight; if you spot-check only a few, check these:

- **Gap window, additive.** `HasGapsIn` writes `d₁ ≤ a_{i+1} − a_i ≤ d₂` as
  `a i + d₁ ≤ a (i+1) ∧ a (i+1) ≤ a i + d₂`, dodging `ℕ`-truncated subtraction — where an isolated
  upper bound `a (i+1) − a i ≤ d₂` would underflow to `0 ≤ d₂` and silently admit negative gaps. For
  `1 ≤ d₁` it also forces `A` strictly increasing.
- **Sumset with repetition.** `kFoldSumset` ranges over arbitrary `f : Fin k → ℕ` with no
  injectivity, so summands may repeat — the intended `kA`, not the smaller distinct-summand set.
- **Quantifier order.** `Question := ∃ r, ∀ B, ∃ A …` places `A` after `B` — "for every `B` there is
  an `A`", not the easier `∃ A ∀ B`.
- **Ratio over `ℕ` (machine-checked bridge).** The site says "an integer `r`"; quantifying `r : ℕ`
  loses no existence content, and this is now proved, not just argued: the frozen file defines the
  integer form `QuestionInt` and proves `question_iff_questionInt : Question ↔ QuestionInt`, so the
  dichotomy holds verbatim for the literal integer phrasing (`erdos_1112_int`).
- **A genuine, non-vacuous `↔`.** Both directions are separately witnessed — existence by the
  explicit ratio `192·d₂` when `d₂ ≥ k+1`, strong non-existence (no prescribed pointwise lower-ratio
  growth sequence for `B` suffices) when `d₂ ≤ k` — and each side of the iff is inhabited.

This certifies the *statement*. That the theorems are actually proved — `sorry`-free, standard axioms
only — is the separate `lake build` check below.
The full decision-by-decision argument, the informal ↔ Lean ↔ file correspondence table, and the
non-vacuity witnesses are in **§6 of the paper** ([`paper/erdos1112.pdf`](paper/erdos1112.pdf)).

## Download and verify

```console
$ git clone https://github.com/beetree/math_erdos_1112
$ cd math_erdos_1112/lean

$ cat lean-toolchain                    # pinned compiler
leanprover/lean4:v4.27.0

$ lake exe cache get                    # download the pinned Mathlib prebuilt
...

$ lake build                            # compiles all 50 proof files
...
Build completed successfully.

$ grep -rn 'sorry$' Erdos1112Proof --include='*.lean'    # no proof sorries: no output
$
```

The trust base — which axioms the proof rests on, and why nothing else is admitted — is covered in
§6 of the paper ([`paper/erdos1112.pdf`](paper/erdos1112.pdf)), Trust base.

Prefer not to build it yourself? A public run of this `lake build` — completing with no `sorry`s — is
inspectable in one click as a
[Kaggle notebook](https://www.kaggle.com/code/johanland/erdos-1112?scriptVersionId=333092350).

---

# Paper proof

The human-readable proof is the paper, **[`paper/erdos1112.pdf`](paper/erdos1112.pdf)** (source
[`paper/erdos1112.tex`](paper/erdos1112.tex)). It establishes the dichotomy — $r_k(d_1, d_2)$ exists
iff $d_2 \ge k+1$ — in four stages: an existence construction, a non-existence reduction, the finite
subset-sum theorem the reduction lands on, and the assembly. The overview below maps each stage to
its section of the paper and to the Lean files that check it.

### 1 · Existence — a construction when $d_2 \ge k+1$
A Beatty/nested-interval construction places $A$ so its $k$-fold sumset threads the gaps a lacunary
$B$ must leave, giving the explicit bound $r_k \le 192\,d_2$.
→ **Paper:** §2 · **Lean:** [`lean/Erdos1112Proof/Existence/`](lean/Erdos1112Proof/Existence)

### 2 · Non-existence — reduction to a finite lemma when $d_2 \le k$
A word-combinatorial analysis (balanced words, Morse–Hedlund, Sturmian ladders) plus an amortized
"slot" argument reduces the strong non-existence statement to a single finite additive-combinatorics
lemma, (SHARP).
→ **Paper:** §3 · **Lean:** [`lean/Erdos1112Proof/NonEx/`](lean/Erdos1112Proof/NonEx)

### 3 · The (SHARP) lemma — the additive-combinatorics core
**(SHARP):** every finite set $G$ of at least three positive integers with $\gcd(G) = 1$ and
$\max(G) = M$ admits a multiset of at most $M - 1$ of its elements whose subset sums contain $M$
consecutive integers. Proved in full via a six-branch decision tree (D / P / L / E / T / B). Its
*finite certificate layer* is cross-checked by two separate Python harnesses (sharing no code) and
by the Lean kernel.
→ **Paper:** §4 · **Lean:** [`lean/Erdos1112Proof/Sharp/`](lean/Erdos1112Proof/Sharp) · **Reproduce (Python):** [`paper/scripts/`](paper/scripts)

### 4 · Assembly
The three Lean-facing theorems — `erdos_1112`, `erdos_1112_existence_bound`, and
`erdos_1112_strong_nonexistence` — stated directly in terms of the frozen definitions and assembled
from the two halves.
→ **Paper:** §5 · **Lean:** [`lean/Erdos1112Proof/Final.lean`](lean/Erdos1112Proof/Final.lean)

## Proof map

| Part | Paper | Formal (Lean) |
|---|---|---|
| Overview & statement faithfulness | §1, §6 | [`lean/Erdos1112.lean`](lean/Erdos1112.lean) (statement) |
| I — Existence | §2 | [`Existence/`](lean/Erdos1112Proof/Existence) |
| II — Non-existence | §3 | [`NonEx/`](lean/Erdos1112Proof/NonEx) |
| III — bounded subset-sum theorem | §4 | [`Sharp/`](lean/Erdos1112Proof/Sharp) |
| IV — Assembly | §5 | [`Final.lean`](lean/Erdos1112Proof/Final.lean) |
| Verification / trust base | §6, Appendix A · [Python harnesses](paper/scripts) | [`AxiomsCheck.lean`](lean/Erdos1112Proof/AxiomsCheck.lean) |
| Certificate tables | Appendix B · [canonical data](paper/data/certificate-data.md) | — |

The full lemma-by-lemma correspondence (paper result → Lean declaration → file) is in
Appendix C of the paper.

---

## Authorship & provenance

**Author:** Johan Land. **Date:** July 5, 2026.

This work is human-orchestrated. The core mathematics was carried out by Claude (Fable 5 and
Opus 4.8) as the reasoning agent; GPT-5.5 and Gemini 3.1 were consulted for advice and adversarial
review. Johan Land directed and audited the work throughout and takes responsibility for the result;
the Lean kernel provides independent machine-checking of the formal proof.

## License

Licensed under the [Apache License 2.0](LICENSE) (see also [`NOTICE`](NOTICE)).
