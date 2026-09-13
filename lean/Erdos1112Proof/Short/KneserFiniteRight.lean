/-
The finite-`B` case of the weak pairwise Kneser law, for the density route
documented in `Short/KneserDensity/README.md`: a finite `B` contributes
`o(n)` to the count `A(n) + B(n)`, so the joint density
`twoFoldLowerDensity A B` collapses to the plain density `lowerDensity A`
outright (`liminf_add_of_tendsto_zero`, the same analytic fact used to
prove the `e`-transform's own density invariance in
`KneserDensity/ETransform.lean`). Combined with `0 ∈ B ⟹ A ⊆ A + B`, this
gives the density half of the weak pairwise Kneser law `hkn`
(`Short/DensityIteration.lean`) directly whenever `B` is finite.

The sequence version generalizes this to any stage of a process with
invariant joint density and first component inside an ambient sumset: if
the joint density there still equals the original one and the first
component still sits inside the ambient sumset, a finite second component
at that stage already forces the density alternative for the whole
process. Contrapositively (`infinite_of_not_le_lowerDensity`), whenever the
density alternative fails, every later second component in the sequence
must be infinite.
-/
import Mathlib
import Erdos1112Proof.Short.KneserDensity.Defs
import Erdos1112Proof.Short.DensityIteration

namespace Erdos1112.Proof.Short.KneserFiniteRight

open Erdos1112.Proof.Short.KneserDensity
open Erdos1112.Proof.Short
open Filter
open scoped Pointwise

/-! ### 1. A finite set contributes a vanishing count -/

/-- **A finite set has vanishing count density.** `posCount B n` is bounded by
the fixed constant `B.ncard` for every `n` (a finite set can never contribute
more elements to any window than its total size), so `posCount B n / n → 0`. -/
theorem tendsto_posCount_div_atTop_of_finite {B : Set ℕ} (hB : B.Finite) :
    Tendsto (fun n : ℕ => (posCount B n : ℝ) / n) atTop (nhds 0) := by
  apply tendsto_bounded_div_atTop_nhds_zero (M := (B.ncard : ℝ))
  filter_upwards with n
  have hle : posCount B n ≤ B.ncard := by
    unfold posCount
    exact Set.ncard_le_ncard Set.inter_subset_left hB
  rw [abs_of_nonneg (by positivity)]
  exact_mod_cast hle

/-! ### 2. The joint density collapses to the first set's density -/

/-- **Finite-right collapse.** If `B` is finite, the two-fold density
`twoFoldLowerDensity A B` equals the plain density `lowerDensity A`: the
`B`-count is `o(n)`, so it drops out of the `liminf`
(`liminf_add_of_tendsto_zero`). This is a direct, unconditional analytic fact
about *any* finite `B` — no properties of `A`, no `0 ∈ B`, no finiteness of any
transform process, and in particular no Frobenius/numerical-semigroup argument
about a fixed point of the `e`-transform sequence. -/
theorem twoFoldLowerDensity_eq_lowerDensity_of_finite_right {A B : Set ℕ}
    (hB : B.Finite) : twoFoldLowerDensity A B = lowerDensity A := by
  have hv : Tendsto (fun n : ℕ => (posCount B n : ℝ) / n) atTop (nhds 0) :=
    tendsto_posCount_div_atTop_of_finite hB
  have hkey := liminf_add_of_tendsto_zero (u := fun n : ℕ => (posCount A n : ℝ) / n)
    (posCountDiv_isBoundedUnder_ge A) (posCountDiv_isBoundedUnder_le A) hv
  have heq : (fun n : ℕ => ((posCount A n : ℝ) + posCount B n) / n) =
      fun n : ℕ => (posCount A n : ℝ) / n + (posCount B n : ℝ) / n := by
    funext n; rw [add_div]
  unfold twoFoldLowerDensity lowerDensity
  rw [heq]
  exact hkey

/-! ### 3. The density alternative of `hkn`, directly, whenever `B` is finite -/

/-- **The density half of `hkn`'s target inequality, in joint-density form, for
finite `B`.** If `0 ∈ B`, then `A ⊆ A + B`, so `lowerDensity A ≤
lowerDensity (A+B)` by monotonicity; combined with the collapse above,
`twoFoldLowerDensity A B ≤ lowerDensity (A+B)`. -/
theorem twoFoldLowerDensity_le_lowerDensity_add_of_finite_right {A B : Set ℕ}
    (hB : B.Finite) (h0 : 0 ∈ B) :
    twoFoldLowerDensity A B ≤ lowerDensity (A + B) := by
  have hsub : A ⊆ A + B := fun a ha => Set.mem_add.mpr ⟨a, ha, 0, h0, by ring⟩
  rw [twoFoldLowerDensity_eq_lowerDensity_of_finite_right hB]
  exact lowerDensity_mono hsub

/-- **`hkn`'s exact first disjunct, for finite `B`.** Chains the two-fold
super-additivity `add_lowerDensity_le_twoFoldLowerDensity` (already proved
unconditionally in `Short/DensityIteration.lean`) with the bound above, giving
the precise inequality `hkn` needs on its left branch, outright and
unconditionally, whenever `B` happens to be finite. -/
theorem hkn_of_finite_right {A B : Set ℕ} (hB : B.Finite) (h0 : 0 ∈ B) :
    lowerDensity A + lowerDensity B ≤ lowerDensity (A + B) :=
  (add_lowerDensity_le_twoFoldLowerDensity A B).trans
    (twoFoldLowerDensity_le_lowerDensity_add_of_finite_right hB h0)

/-! ### 4. The sequence version: a finite stage anywhere forces the density
alternative for the whole (invariant-joint-density) process -/

/-- **Generalized to any stage of an invariant-joint-density process.** If some
pair `(A', B')` has the same joint density as the original `(A, B)` — as holds
at every stage of the ordinary-`e`-transform sequence, by the unconditional
density invariance `twoFoldLowerDensity_eTransform_eq` — `A'` sits inside the
ambient set `C` (e.g. `C = A + B`, since every stage's first component stays
inside the original sumset), and `B'` is finite, then the joint density of the
*original* pair is already bounded by the density of `C`. No `0 ∈ B'` is needed:
monotonicity from `A' ⊆ C` alone suffices once step 2 replaces the joint density
by `lowerDensity A'`. -/
theorem twoFoldLowerDensity_le_lowerDensity_of_finite_stage
    {A B A' B' C : Set ℕ} (hinv : twoFoldLowerDensity A' B' = twoFoldLowerDensity A B)
    (hsub : A' ⊆ C) (hB' : B'.Finite) :
    twoFoldLowerDensity A B ≤ lowerDensity C := by
  rw [← hinv, twoFoldLowerDensity_eq_lowerDensity_of_finite_right hB']
  exact lowerDensity_mono hsub

/-- **Resolves the review's finding.** For a sequence of stages
`A' B' : ℕ → Set ℕ` all sharing the original joint density and all having first
component inside the ambient `C`: if the density alternative
`twoFoldLowerDensity A B ≤ lowerDensity C` *fails*, then **every** stage's second
component `B' n` is infinite. Whichever stage `WEAK_KNESER_PLAN.md`'s absorbed-block
step is applied to, either the elementary density bound above already finishes
the proof, or that stage's `B'` is guaranteed infinite — exactly the missing
disjunction `Short/KneserBlocks.lean`'s `B.Infinite` hypothesis needed. -/
theorem infinite_of_not_le_lowerDensity
    {A B C : Set ℕ} {A' B' : ℕ → Set ℕ}
    (hinv : ∀ n, twoFoldLowerDensity (A' n) (B' n) = twoFoldLowerDensity A B)
    (hsub : ∀ n, A' n ⊆ C)
    (hfail : ¬ twoFoldLowerDensity A B ≤ lowerDensity C) :
    ∀ n, (B' n).Infinite := by
  intro n
  by_contra hfin
  rw [Set.not_infinite] at hfin
  exact hfail (twoFoldLowerDensity_le_lowerDensity_of_finite_stage (hinv n) (hsub n) hfin)

end Erdos1112.Proof.Short.KneserFiniteRight
