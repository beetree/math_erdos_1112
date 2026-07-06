# Erdős Problem #1112

From [erdosproblems.com/1112](https://www.erdosproblems.com/1112) (verbatim):

> Let $1 \le d_1 < d_2$ and $k \ge 3$. Does there exist an integer $r$ such that if
> $B = \{b_1 < \cdots\}$ is a lacunary sequence of positive integers with $b_{i+1} \ge r b_i$ then
> there exists a sequence of positive integers $A = \{a_1 < \cdots\}$ such that
> $d_1 \le a_{i+1} - a_i \le d_2$ for all $i \ge 1$ and $(kA) \cap B = \emptyset$, where $kA$ is the
> $k$-fold sumset?

Below is a complete resolution, in two forms:

- a **[Lean proof](#lean-proof)** — the machine-checked formalization, with a one-command way to verify it yourself;
- a **[paper proof](#paper-proof)** — the human-readable argument, with each step linked to the Lean file that checks it.

---

# Lean proof

## The Lean formulation

The problem is transcribed into Lean in the frozen statement file
[`lean/Erdos1112.lean`](lean/Erdos1112.lean) — see [Statement faithfulness](proof/statement-faithfulness.md)
for why this encoding is faithful (summarized below). The core definitions:

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
- **Ratio over `ℕ`.** Quantifying `r : ℕ` preserves the existence question for an integer ratio
  witness; `RatioWorks.mono` (a larger `r` only shrinks the admissible class of `B`) is the
  machine-checked piece of that reduction.
- **A genuine, non-vacuous `↔`.** Both directions are separately witnessed — existence by the
  explicit ratio `192·d₂` when `d₂ ≥ k+1`, strong non-existence (no prescribed pointwise lower-ratio
  growth sequence for `B` suffices) when `d₂ ≤ k` — and each side of the iff is inhabited.

This certifies the *statement*. That the theorems are actually proved — `sorry`-free, standard axioms
only — is the separate `lake build` check below.
The full decision-by-decision argument, the informal ↔ Lean ↔ file correspondence table, and the
non-vacuity witnesses are in [**Statement faithfulness**](proof/statement-faithfulness.md).

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
[Appendix D](proof/appendix-D-lean.md) (§D.2, Trust base).

---

# Paper proof

The proof establishes the dichotomy — $r_k(d_1, d_2)$ exists iff $d_2 \ge k+1$ — in four stages: an
existence construction, a non-existence reduction, the finite lemma the reduction lands on, and the
assembly. Read them in order, or jump to any one — and from each, jump to the corresponding Lean
files. To read the whole paper in one document, see
[`proof/erdos1112-paper.md`](proof/erdos1112-paper.md) (all parts and appendices, compiled).

### 1 · Existence — a construction when $d_2 \ge k+1$
A Beatty/nested-interval construction places $A$ so its $k$-fold sumset threads the gaps a lacunary
$B$ must leave, giving the explicit bound $r_k \le 192\,d_2$.
→ **Read:** [Part I](proof/01-existence.md) · **Lean:** [`lean/Erdos1112Proof/Existence/`](lean/Erdos1112Proof/Existence)

### 2 · Non-existence — reduction to a finite lemma when $d_2 \le k$
A word-combinatorial analysis (balanced words, Morse–Hedlund, Sturmian ladders) plus an amortized
"slot" argument reduces the strong non-existence statement to a single finite additive-combinatorics
lemma, (SHARP).
→ **Read:** [Part II](proof/02-nonexistence.md) · **Lean:** [`lean/Erdos1112Proof/NonEx/`](lean/Erdos1112Proof/NonEx)

### 3 · The (SHARP) lemma — the additive-combinatorics core
**(SHARP):** every finite set $G$ of at least three positive integers with $\gcd(G) = 1$ and
$\max(G) = M$ admits a multiset of at most $M - 1$ of its elements whose subset sums contain $M$
consecutive integers. Proved in full via a six-branch decision tree (D / P / L / E / T / B). Its
*finite certificate layer* is cross-checked by two separate Python harnesses (sharing no code) and
by the Lean kernel.
→ **Read:** [Part III](proof/03-sharp.md) · **Lean:** [`lean/Erdos1112Proof/Sharp/`](lean/Erdos1112Proof/Sharp) · **Reproduce (Python):** [Appendix C](proof/appendix-C-scripts.md)

### 4 · Assembly
The three Lean-facing theorems — `erdos_1112`, `erdos_1112_existence_bound`, and
`erdos_1112_strong_nonexistence` — stated directly in terms of the frozen definitions and assembled
from the two halves.
→ **Read:** [Part IV](proof/04-assembly.md) · **Lean:** [`lean/Erdos1112Proof/Final.lean`](lean/Erdos1112Proof/Final.lean)

## Proof map

| Part | Prose | Formal (Lean) |
|---|---|---|
| Statement faithfulness | [statement-faithfulness](proof/statement-faithfulness.md) | [`lean/Erdos1112.lean`](lean/Erdos1112.lean) (statement) |
| Overview & notation | [00-overview](proof/00-overview.md) | [`lean/Erdos1112.lean`](lean/Erdos1112.lean) (statement) |
| I — Existence | [01-existence](proof/01-existence.md) | [`Existence/`](lean/Erdos1112Proof/Existence) |
| II — Non-existence | [02-nonexistence](proof/02-nonexistence.md) | [`NonEx/`](lean/Erdos1112Proof/NonEx) |
| III — (SHARP) | [03-sharp](proof/03-sharp.md) | [`Sharp/`](lean/Erdos1112Proof/Sharp) |
| IV — Assembly | [04-assembly](proof/04-assembly.md) | [`Final.lean`](lean/Erdos1112Proof/Final.lean) |
| Verification | [Appendix A](proof/appendix-A-verification.md) · [Appendix C](proof/appendix-C-scripts.md) · [Appendix D](proof/appendix-D-lean.md) | [`AxiomsCheck.lean`](lean/Erdos1112Proof/AxiomsCheck.lean) |
| Certificate tables | [Appendix B](proof/appendix-B-tables.md) | — |

The full lemma-by-lemma correspondence (paper result → Lean declaration → file) is in
[Appendix D §D.4](proof/appendix-D-lean.md).

---

## Authorship & provenance

**Author:** Johan Land. **Date:** July 5, 2026.

This work is human-orchestrated. The core mathematics was carried out by Claude (Fable 5 and
Opus 4.8) as the reasoning agent; GPT-5.5 and Gemini 3.1 were consulted for advice and adversarial
review. Johan Land directed and audited the work throughout and takes responsibility for the result;
the Lean kernel provides independent machine-checking of the formal proof.

## License

Licensed under the [Apache License 2.0](LICENSE) (see also [`NOTICE`](NOTICE)).
