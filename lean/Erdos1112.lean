/-
Erdős Problem 1112 — formal statement.

*Reference:* [erdosproblems.com/1112](https://www.erdosproblems.com/1112)

The problem, verbatim from the site:

  "Let $1 \le d_1 < d_2$ and $k \ge 3$. Does there exist an integer $r$ such
  that if $B = \{b_1 < b_2 < \cdots\}$ is a lacunary sequence with
  $b_{i+1} \ge r b_i$ then there exists $A = \{a_1 < a_2 < \cdots\}$ with
  $d_1 \le a_{i+1} - a_i \le d_2$ for all $i$ and $(kA) \cap B = \emptyset$?"

Here $kA = \{x_1 + \cdots + x_k : x_1, \ldots, x_k \in A\}$ is the $k$-fold
sumset (repetitions allowed), and $A$, $B$ are infinite sets of positive
integers, encoded below as strictly increasing sequences `ℕ → ℕ` (0-indexed).

Encoding notes (reviewed):
* `IsLacunaryWith` requires `StrictMono b` explicitly, so the class of
  admissible `B` matches the page's `{b₁ < b₂ < ⋯}` notation for *every*
  candidate ratio `r`, not only `r ≥ 2` (where the ratio condition would
  force it anyway).
* `r` is quantified over `ℕ` rather than `ℤ`: the admissible class of `B`
  shrinks as `r` grows, so if any integer ratio works then any larger one
  does; hence the existential questions over `ℤ` and `ℕ` coincide.
* The gap condition is phrased additively (`a i + d₁ ≤ a (i+1)`) to avoid
  truncated natural-number subtraction; with `1 ≤ d₁` it is equivalent to
  `d₁ ≤ a (i+1) − a i ≤ d₂` and forces `A` strictly increasing.

Status: the dichotomy `erdos_1112`, proved in `Erdos1112Proof/Final.lean`
against the definitions in this file, resolves the problem with a complete,
`sorry`-free formal proof. The paper proof is in `../proof/`.
-/
import Mathlib

namespace Erdos1112

/-- `B` (as a strictly increasing enumeration of an infinite set of positive
integers) is *lacunary with ratio `r`*: `b₁ ≥ 1`, `b₁ < b₂ < ⋯`, and
`b_{i+1} ≥ r · b_i` for all `i`. -/
def IsLacunaryWith (r : ℕ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, r * b i ≤ b (i + 1)

/-- `A` (as a strictly increasing enumeration of an infinite set of positive
integers) has all consecutive gaps in `[d₁, d₂]`:
`d₁ ≤ a_{i+1} − a_i ≤ d₂` for all `i` (phrased additively; for `1 ≤ d₁`
this forces `A` strictly increasing). -/
def HasGapsIn (d₁ d₂ : ℕ) (a : ℕ → ℕ) : Prop :=
  0 < a 0 ∧ ∀ i, a i + d₁ ≤ a (i + 1) ∧ a (i + 1) ≤ a i + d₂

/-- For `1 ≤ d₁`, the gap condition forces `A` strictly increasing (audit
helper: makes explicit that `A` enumerates an infinite set). -/
lemma HasGapsIn.strictMono {d₁ d₂ : ℕ} {a : ℕ → ℕ} (hd₁ : 1 ≤ d₁)
    (h : HasGapsIn d₁ d₂ a) : StrictMono a :=
  strictMono_nat_of_lt_succ fun i =>
    lt_of_lt_of_le (Nat.lt_add_of_pos_right hd₁) (h.2 i).1

/-- The `k`-fold sumset `kA` of the set enumerated by `a`:
all sums `a_{i₁} + ⋯ + a_{i_k}` (indices arbitrary, repetitions allowed). -/
def kFoldSumset (k : ℕ) (a : ℕ → ℕ) : Set ℕ :=
  { n | ∃ f : Fin k → ℕ, n = ∑ j, a (f j) }

/-- The property asked for by the problem, for given `k`, `d₁`, `d₂` and a
candidate `r`: *every* lacunary sequence `B` with ratio `r` admits a set `A`
with gaps in `[d₁, d₂]` such that `(kA) ∩ B = ∅`. -/
def RatioWorks (k d₁ d₂ r : ℕ) : Prop :=
  ∀ b : ℕ → ℕ, IsLacunaryWith r b →
    ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧
      Disjoint (kFoldSumset k a) (Set.range b)

/-- `RatioWorks` is monotone in the ratio: a larger `r` only shrinks the class
of admissible `B`. This machine-checks the reduction from "an integer `r`" to
`r : ℕ` in `Question`: any integer witness may be replaced by any larger
natural one. -/
lemma RatioWorks.mono {k d₁ d₂ r r' : ℕ} (hrr' : r ≤ r')
    (h : RatioWorks k d₁ d₂ r) : RatioWorks k d₁ d₂ r' := by
  intro b hb
  exact h b ⟨hb.1, hb.2.1, fun i => (Nat.mul_le_mul hrr' le_rfl).trans (hb.2.2 i)⟩

/-- **Erdős Problem 1112** (erdosproblems.com/1112), verbatim question:

"Let `1 ≤ d₁ < d₂` and `k ≥ 3`. Does there exist an integer `r` such that if
`B = {b₁ < b₂ < ⋯}` is a lacunary sequence with `b_{i+1} ≥ r·b_i` then there
exists `A = {a₁ < a₂ < ⋯}` with `d₁ ≤ a_{i+1} − a_i ≤ d₂` for all `i` and
`(kA) ∩ B = ∅`?"

I.e., for which `(k, d₁, d₂)` does `∃ r, RatioWorks k d₁ d₂ r` hold?
(Quantifying `r` over `ℕ` is equivalent to quantifying over `ℤ`; see the
header note.) -/
def Question (k d₁ d₂ : ℕ) : Prop :=
  ∃ r : ℕ, RatioWorks k d₁ d₂ r

/-- `B` is lacunary with a *varying* ratio sequence `R`:
`b_{i+1} ≥ R i · b_i` for all `i`. -/
def IsVarLacunaryWith (R : ℕ → ℕ) (b : ℕ → ℕ) : Prop :=
  0 < b 0 ∧ StrictMono b ∧ ∀ i, R i * b i ≤ b (i + 1)

/-- Constant-ratio varying lacunarity is exactly fixed-ratio lacunarity
(audit helper: the bridge used when instantiating the strong non-existence
theorem to refute `RatioWorks` at a constant ratio). -/
lemma isVarLacunaryWith_const_iff {r : ℕ} {b : ℕ → ℕ} :
    IsVarLacunaryWith (fun _ => r) b ↔ IsLacunaryWith r b :=
  Iff.rfl

end Erdos1112
