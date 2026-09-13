/-
Translation / tail-cut invariance of `lowerDensity` and `twoFoldLowerDensity`
(`Short/KneserDensity/Defs.lean`), needed for step 7 of the weak-Kneser plan
(`/tmp/erdos1112-agents/WEAK_KNESER_PLAN.md`): "Shift that first component
down by `x` and discard its finite prefix ... Translation/discarding a
finite prefix leaves density unchanged."

This file owns exactly the elementary shift step: it does *not* touch
residue compression, the cofinite-set/AP-tail argument, or any other part
of the plan (those are other workers' files, read-only here).

No `sorry`, no custom `axiom`; every boundary case (`N = 0`, `x` arbitrary
relative to `N`) is derived by the same general argument, not assumed.
-/
import Mathlib
import Erdos1112Proof.Short.KneserDensity.Defs
import Erdos1112Proof.Short.DensityIteration

namespace Erdos1112.Proof.Short

open Erdos1112.Proof.Short.KneserDensity
open Filter
open scoped Pointwise

/-! ### The shift operations -/

/-- `A` shifted down by `x`: reindex the part of `A` at or above `x` to
start at `0`. -/
def shiftedDown (A : Set ℕ) (x : ℕ) : Set ℕ := {n : ℕ | x + n ∈ A}

/-- `A` shifted up by `x`. -/
def shiftedUp (x : ℕ) (A : Set ℕ) : Set ℕ := (fun n => x + n) '' A

@[simp] lemma mem_shiftedDown {A : Set ℕ} {x n : ℕ} : n ∈ shiftedDown A x ↔ x + n ∈ A := Iff.rfl

lemma mem_shiftedUp {x m : ℕ} {A : Set ℕ} : m ∈ shiftedUp x A ↔ ∃ n ∈ A, x + n = m := by
  simp [shiftedUp]

/-- Boundary case named explicitly, as requested: `0` lands in the shifted
set exactly when the shift point itself was in `A`. -/
@[simp] lemma zero_mem_shiftedDown_iff {A : Set ℕ} {x : ℕ} : 0 ∈ shiftedDown A x ↔ x ∈ A := by
  simp [shiftedDown]

/-- Shifting down by `x` and back up by `x` recovers `A` exactly (no
boundary loss: every element of `A`, including any that lie below `x`, is
just not in the image of `shiftedUp x`, so this is about the round trip
`shiftedUp ∘ shiftedDown`, not the other order). -/
@[simp] lemma shiftedDown_shiftedUp (x : ℕ) (A : Set ℕ) : shiftedDown (shiftedUp x A) x = A := by
  ext n
  simp only [mem_shiftedDown, mem_shiftedUp]
  constructor
  · rintro ⟨a, ha, heq⟩
    have : a = n := by omega
    rwa [this] at ha
  · exact fun hn => ⟨n, hn, rfl⟩

/-- `(shiftedDown A x) + B`, shifted back up by `x`, lands inside `A + B`:
the elementary sum-containment fact behind the plan's "absorb such an
interval into a later pair" step. -/
lemma shiftedUp_add_shiftedDown_subset (A B : Set ℕ) (x : ℕ) :
    shiftedUp x (shiftedDown A x + B) ⊆ A + B := by
  rintro _ ⟨s, hs, rfl⟩
  rcases hs with ⟨n, hn, b, hb, rfl⟩
  exact ⟨x + n, hn, b, hb, by ring⟩

/-! ### The exact `posCount` window shift -/

/-- **The window shift**: `(shiftedDown A x)(N) = A(x+N) - A(x)`, exact for
every `x, N : ℕ` (in particular `N = 0` and `x` arbitrary relative to `N`
are not special-cased — the bijection argument below proves the identity
uniformly). -/
theorem posCount_shiftedDown (A : Set ℕ) (x N : ℕ) :
    posCount (shiftedDown A x) N = posCount A (x + N) - posCount A x := by
  have himg : (fun n => x + n) '' (shiftedDown A x ∩ Set.Icc 1 N) = A ∩ Set.Icc (x + 1) (x + N) := by
    ext m
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_Icc, mem_shiftedDown]
    constructor
    · rintro ⟨n, ⟨hn, hn1, hnN⟩, rfl⟩
      exact ⟨hn, by omega, by omega⟩
    · rintro ⟨hm, hm1, hmN⟩
      exact ⟨m - x, ⟨by rw [show x + (m - x) = m by omega]; exact hm, by omega, by omega⟩, by omega⟩
  have hcard : posCount (shiftedDown A x) N = (A ∩ Set.Icc (x + 1) (x + N)).ncard := by
    show (shiftedDown A x ∩ Set.Icc 1 N).ncard = _
    rw [← himg, Set.ncard_image_of_injective _ (add_right_injective x)]
  have hwin := posCount_window_add A (show x ≤ x + N by omega)
  omega

/-! ### The error term, and its two consequences -/

/-- The correction between `A(x+n)` and `A(n) + A(x)` is bounded by `x` (in
absolute value) and hence, divided by `n`, tends to `0`. This single fact
drives both `lowerDensity` and `twoFoldLowerDensity` shift-invariance below;
`B` never enters it, since only `A` is being shifted. -/
private lemma tendsto_shiftedDown_error (A : Set ℕ) (x : ℕ) :
    Tendsto (fun n : ℕ => ((posCount A (x + n) : ℝ) - posCount A n - posCount A x) / n)
      atTop (nhds 0) := by
  apply tendsto_bounded_div_atTop_nhds_zero (M := (x : ℝ))
  filter_upwards with n
  have hmono : posCount A n ≤ posCount A (x + n) := posCount_mono_arg A (by omega)
  have hwin : posCount A (x + n) - posCount A n ≤ x := by
    have h := posCount_window_le A (show n ≤ x + n by omega)
    omega
  have hle : posCount A (x + n) ≤ posCount A n + x := by omega
  have hself : posCount A x ≤ x := posCount_le_self A x
  have hcastge : (posCount A n : ℝ) ≤ posCount A (x + n) := by exact_mod_cast hmono
  have hcastle : (posCount A (x + n) : ℝ) ≤ posCount A n + x := by exact_mod_cast hle
  have hcastself : (posCount A x : ℝ) ≤ x := by exact_mod_cast hself
  have hselfnn : (0 : ℝ) ≤ posCount A x := Nat.cast_nonneg _
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- Rewriting `(shiftedDown A x)(n)` via `posCount_shiftedDown`, cast to `ℝ`
without truncation (`posCount A x ≤ posCount A (x+n)` always holds). -/
private lemma posCount_shiftedDown_cast (A : Set ℕ) (x n : ℕ) :
    (posCount (shiftedDown A x) n : ℝ) = (posCount A (x + n) : ℝ) - posCount A x := by
  have hmono : posCount A x ≤ posCount A (x + n) := posCount_mono_arg A (by omega)
  rw [posCount_shiftedDown, Nat.cast_sub hmono]

/-- **`δ` is invariant under `shiftedDown`.** -/
theorem lowerDensity_shiftedDown (A : Set ℕ) (x : ℕ) :
    lowerDensity (shiftedDown A x) = lowerDensity A := by
  unfold lowerDensity
  have hsplit : (fun n : ℕ => (posCount (shiftedDown A x) n : ℝ) / n) =
      (fun n : ℕ => (posCount A n : ℝ) / n) +
        fun n : ℕ => ((posCount A (x + n) : ℝ) - posCount A n - posCount A x) / n := by
    funext n
    simp only [Pi.add_apply]
    rw [posCount_shiftedDown_cast]
    ring
  rw [hsplit]
  exact liminf_add_of_tendsto_zero (posCountDiv_isBoundedUnder_ge A) (posCountDiv_isBoundedUnder_le A)
    (tendsto_shiftedDown_error A x)

/-- **`δ` is invariant under `shiftedUp`** (the converse direction, via the
round trip `shiftedDown (shiftedUp x A) x = A`). -/
theorem lowerDensity_shiftedUp (x : ℕ) (A : Set ℕ) :
    lowerDensity (shiftedUp x A) = lowerDensity A := by
  have h := lowerDensity_shiftedDown (shiftedUp x A) x
  rw [shiftedDown_shiftedUp] at h
  exact h.symm

/-- `twoFoldLowerDensity` is symmetric (immediate from `posCount A + posCount B
= posCount B + posCount A`). -/
theorem twoFoldLowerDensity_comm (A B : Set ℕ) : twoFoldLowerDensity A B = twoFoldLowerDensity B A := by
  unfold twoFoldLowerDensity
  congr 1
  funext n
  ring

private lemma twoFoldPosCountDiv_isBoundedUnder_ge (A B : Set ℕ) :
    atTop.IsBoundedUnder (· ≥ ·) (fun n : ℕ => ((posCount A n : ℝ) + posCount B n) / n) := by
  refine ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun n => ?_)⟩
  positivity

private lemma twoFoldPosCountDiv_isBoundedUnder_le (A B : Set ℕ) :
    atTop.IsBoundedUnder (· ≤ ·) (fun n : ℕ => ((posCount A n : ℝ) + posCount B n) / n) := by
  refine ⟨2, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun n => ?_)⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · rw [div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)]
    have h1 : (posCount A n : ℝ) ≤ n := by exact_mod_cast posCount_le_self A n
    have h2 : (posCount B n : ℝ) ≤ n := by exact_mod_cast posCount_le_self B n
    nlinarith

/-- **`δ(·,B)` is invariant under shifting the first argument down.** Only
`A`'s window moves; `B`'s contribution cancels exactly in the correction
term, which is why `tendsto_shiftedDown_error` needs no `B`-dependence. -/
theorem twoFoldLowerDensity_shiftedDown_left (A B : Set ℕ) (x : ℕ) :
    twoFoldLowerDensity (shiftedDown A x) B = twoFoldLowerDensity A B := by
  unfold twoFoldLowerDensity
  have hsplit : (fun n : ℕ => ((posCount (shiftedDown A x) n : ℝ) + posCount B n) / n) =
      (fun n : ℕ => ((posCount A n : ℝ) + posCount B n) / n) +
        fun n : ℕ => ((posCount A (x + n) : ℝ) - posCount A n - posCount A x) / n := by
    funext n
    simp only [Pi.add_apply]
    rw [posCount_shiftedDown_cast]
    ring
  rw [hsplit]
  exact liminf_add_of_tendsto_zero (twoFoldPosCountDiv_isBoundedUnder_ge A B)
    (twoFoldPosCountDiv_isBoundedUnder_le A B) (tendsto_shiftedDown_error A x)

/-- **`δ(A,·)` is invariant under shifting the second argument down**
(via `twoFoldLowerDensity_comm` and the left-hand version). -/
theorem twoFoldLowerDensity_shiftedDown_right (A B : Set ℕ) (y : ℕ) :
    twoFoldLowerDensity A (shiftedDown B y) = twoFoldLowerDensity B A := by
  rw [twoFoldLowerDensity_comm A (shiftedDown B y), twoFoldLowerDensity_shiftedDown_left B A y]

/-- **`δ(·,·)` is invariant under shifting both arguments down, by possibly
different offsets** — the joint form needed for step 7 (both `A_j` and the
compressed `B` may be re-based independently). -/
theorem twoFoldLowerDensity_shiftedDown_both (A B : Set ℕ) (x y : ℕ) :
    twoFoldLowerDensity (shiftedDown A x) (shiftedDown B y) = twoFoldLowerDensity A B := by
  rw [twoFoldLowerDensity_shiftedDown_left A (shiftedDown B y) x,
    twoFoldLowerDensity_shiftedDown_right A B y, twoFoldLowerDensity_comm B A]

/-! ### AP-tail translation transport -/

/-- `HasAPTail` transports forward along `shiftedUp` (just shift the AP's
base point). -/
theorem HasAPTail.shiftedUp {S : Set ℕ} (x : ℕ) (h : HasAPTail S) : HasAPTail (shiftedUp x S) := by
  obtain ⟨q, hq, x0, hx0⟩ := h
  exact ⟨q, hq, x + x0, fun j => ⟨x0 + q * j, hx0 j, by ring⟩⟩

/-- **AP-tail translation transport**: if the shifted-down-and-summed set
`(shiftedDown A x) + B` has an AP tail, so does the original `A + B`. This
is exactly the fact step 7 needs to lift a cofinite compressed sumset back
to an AP tail of `A + B` (the residue-compression side of that step is
handled elsewhere; this file supplies only the shift transport). -/
theorem HasAPTail.of_shiftedDown_add {A B : Set ℕ} {x : ℕ}
    (h : HasAPTail (shiftedDown A x + B)) : HasAPTail (A + B) :=
  HasAPTail.mono (shiftedUp_add_shiftedDown_subset A B x) (HasAPTail.shiftedUp x h)

end Erdos1112.Proof.Short
