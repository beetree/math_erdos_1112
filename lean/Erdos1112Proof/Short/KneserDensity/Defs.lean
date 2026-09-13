/-
Core definitions for the Kneser density shortcut, matching the
Introduction of the primary source used for this development: John B.
Lane, *A New Approach to Kneser's Theorem on Asymptotic Density*, Ph.D.
dissertation, Virginia Polytechnic Institute and State University, 1973.
See `Short/KneserDensity/README.md` for the full source list and links.

Lane's convention (in force throughout his dissertation, and kept here):
sets of non-negative integers are taken to contain zero unless stated
otherwise. This is not baked into the `Set ℕ` type itself (Lean has no
subtyping for that); instead each downstream lemma that needs `0 ∈ A`
states it as an explicit hypothesis, exactly where Lane's blanket
convention is actually used.
-/
import Mathlib

namespace Erdos1112.Proof.Short.KneserDensity

open scoped Pointwise

/-- **`A(n)`** (Lane, Introduction p. 1): "the number of positive elements
of `A` which are less than or equal to `n`". Deliberately excludes `0` even
when `0 ∈ A`. -/
noncomputable def posCount (A : Set ℕ) (n : ℕ) : ℕ := (A ∩ Set.Icc 1 n).ncard

@[simp] lemma posCount_zero (A : Set ℕ) : posCount A 0 = 0 := by
  simp [posCount]

lemma posCount_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) : posCount A n ≤ posCount B n :=
  Set.ncard_le_ncard (Set.inter_subset_inter_left _ h) ((Set.finite_Icc 1 n).inter_of_right _)

lemma posCount_le_self (A : Set ℕ) (n : ℕ) : posCount A n ≤ n := by
  refine (Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Icc 1 n)).trans ?_
  rw [show Set.Icc 1 n = (↑(Finset.Icc 1 n) : Set ℕ) by simp, Set.ncard_coe_finset]
  simp

/-- **`A(y) = A(x) + |A ∩ (x,y]|`** for `x ≤ y`: splitting the count at `x`.
The window `A ∩ Icc (x+1) y` is exactly "the elements of `A` counted by
`A(y)` but not by `A(x)`" (Lane's implicit device throughout the proof of
Theorem 4, part III, p. 8). -/
lemma posCount_window_add (A : Set ℕ) {x y : ℕ} (hxy : x ≤ y) :
    posCount A y = posCount A x + (A ∩ Set.Icc (x + 1) y).ncard := by
  have hsplit : A ∩ Set.Icc 1 y = (A ∩ Set.Icc 1 x) ∪ (A ∩ Set.Icc (x + 1) y) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_union]
    constructor
    · rintro ⟨hz, hz1, hzy⟩
      by_cases h : z ≤ x
      · exact Or.inl ⟨hz, hz1, h⟩
      · exact Or.inr ⟨hz, by omega, hzy⟩
    · rintro (⟨hz, hz1, hzx⟩ | ⟨hz, hz1, hzy⟩)
      · exact ⟨hz, hz1, hzx.trans hxy⟩
      · exact ⟨hz, by omega, hzy⟩
  have hdisj : Disjoint (A ∩ Set.Icc 1 x) (A ∩ Set.Icc (x + 1) y) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨_, _, hzx⟩ ⟨_, hzx1, _⟩
    omega
  unfold posCount
  rw [hsplit, Set.ncard_union_eq hdisj ((Set.finite_Icc 1 x).inter_of_right _)
    ((Set.finite_Icc (x+1) y).inter_of_right _)]

/-- **`δ(A)`** (Lane, Introduction p. 1): the (lower) asymptotic density of
`A`, `liminf A(n)/n`. -/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun n : ℕ => (posCount A n : ℝ) / n) Filter.atTop

/-- **`δ(A,B)`** (Lane, Introduction p. 1): the two-fold (lower) asymptotic
density of `A` and `B`, `liminf (A(n)+B(n))/n`. -/
noncomputable def twoFoldLowerDensity (A B : Set ℕ) : ℝ :=
  Filter.liminf (fun n : ℕ => ((posCount A n : ℝ) + posCount B n) / n) Filter.atTop

/-- **`A ∼ B`** (Lane, Introduction p. 1): `A` and `B` are asymptotically
equal, i.e. they agree on some tail `[N, ∞)`. -/
def AsymEq (A B : Set ℕ) : Prop := ∃ N, ∀ x ≥ N, (x ∈ A ↔ x ∈ B)

@[refl] lemma AsymEq.refl (A : Set ℕ) : AsymEq A A := ⟨0, fun _ _ => Iff.rfl⟩

lemma AsymEq.symm {A B : Set ℕ} (h : AsymEq A B) : AsymEq B A :=
  h.imp fun _ hN x hx => (hN x hx).symm

lemma AsymEq.trans {A B C : Set ℕ} (h1 : AsymEq A B) (h2 : AsymEq B C) : AsymEq A C := by
  obtain ⟨N1, h1⟩ := h1
  obtain ⟨N2, h2⟩ := h2
  exact ⟨max N1 N2, fun x hx =>
    (h1 x (le_of_max_le_left hx)).trans (h2 x (le_of_max_le_right hx))⟩

/-- **`A^(g)`** (Lane, Introduction p. 1): "the union of all residue classes,
mod `g`, which have a representative in `A`". -/
def periodicClosure (A : Set ℕ) (g : ℕ) : Set ℕ := {x : ℕ | ∃ a ∈ A, x ≡ a [MOD g]}

lemma subset_periodicClosure {A : Set ℕ} {g : ℕ} : A ⊆ periodicClosure A g :=
  fun a ha => ⟨a, ha, Nat.ModEq.refl a⟩

/-- If `a` is in `A`, the whole tail of `a`'s residue class mod `g` lies in
`A^(g)`. -/
lemma tail_mod_subset_periodicClosure {A : Set ℕ} {g : ℕ} {a : ℕ} (ha : a ∈ A) :
    {x : ℕ | x % g = a % g} ⊆ periodicClosure A g :=
  fun _ hx => ⟨a, ha, hx⟩

/-! ### Boundedness helpers for `liminf`

`ℝ` is only *conditionally* complete, so every `liminf`/`limsup` comparison
lemma needs explicit `IsBoundedUnder`/`IsCoboundedUnder` side conditions.
Every density sequence we ever compare has the shape `n ↦ f(n) / n` for a
`f : ℕ → ℕ` with `f(n) ≤ C * n`; these two helpers discharge the side
conditions for that shape once and for all. -/

/-- Dividing by a fixed `n : ℕ` (cast to `ℝ`, so `n = 0` harmlessly gives `0`
on both sides) is monotone. -/
lemma div_le_div_of_le_nonneg {n : ℕ} {x y : ℝ} (h : x ≤ y) : x / n ≤ y / n :=
  div_le_div_of_nonneg_right h (Nat.cast_nonneg n)

lemma isBoundedUnder_ge_div {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) :
    Filter.atTop.IsBoundedUnder (· ≥ ·) (fun n : ℕ => u n / n) :=
  ⟨0, Filter.eventually_map.mpr
    (Filter.Eventually.of_forall fun n => div_nonneg (hu n) (Nat.cast_nonneg n))⟩

lemma isCoboundedUnder_ge_div {u : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, u n ≤ C * n) :
    Filter.atTop.IsCoboundedUnder (· ≥ ·) (fun n : ℕ => u n / n) := by
  have hbdd : Filter.atTop.IsBoundedUnder (· ≤ ·) (fun n : ℕ => u n / n) := by
    refine ⟨C, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun n => ?_)⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn, hC]
    · rw [div_le_iff₀ (show (0:ℝ) < n by exact_mod_cast hn)]
      exact h n
  exact hbdd.isCoboundedUnder_ge

/-- Specialization of `isBoundedUnder_ge_div`/`isCoboundedUnder_ge_div` to
`n ↦ (f n : ℝ)/n` for `f : ℕ → ℕ`, the shape every single-set density
sequence has. -/
lemma isBoundedUnder_ge_countDiv (f : ℕ → ℕ) :
    Filter.atTop.IsBoundedUnder (· ≥ ·) (fun n : ℕ => (f n : ℝ) / n) :=
  isBoundedUnder_ge_div fun n => Nat.cast_nonneg (f n)

lemma isCoboundedUnder_ge_countDiv {f : ℕ → ℕ} {C : ℕ} (h : ∀ n, f n ≤ C * n) :
    Filter.atTop.IsCoboundedUnder (· ≥ ·) (fun n : ℕ => (f n : ℝ) / n) :=
  isCoboundedUnder_ge_div (C := C) (Nat.cast_nonneg C) fun n => by exact_mod_cast h n

/-- **Adding a null sequence does not change `liminf`.** The analytic
workhorse behind Lane's Theorem 5 (p. 9-10): each regrouping step there adds
or removes a term that is bounded and divided by `y → ∞`, hence tends to
`0`, and the claim is that this never changes the `liminf`. Needs `u` itself
bounded both ways (our `u`'s are always ratios in `[0, C]`). -/
lemma liminf_add_of_tendsto_zero {u v : ℕ → ℝ}
    (hu1 : Filter.atTop.IsBoundedUnder (· ≥ ·) u) (hu2 : Filter.atTop.IsBoundedUnder (· ≤ ·) u)
    (hv : Filter.Tendsto v Filter.atTop (nhds 0)) :
    Filter.liminf (fun n => u n + v n) Filter.atTop = Filter.liminf u Filter.atTop := by
  have hv1 : Filter.atTop.IsBoundedUnder (· ≥ ·) v := hv.isBoundedUnder_ge
  have hv2 : Filter.atTop.IsBoundedUnder (· ≤ ·) v := hv.isBoundedUnder_le
  have hv1' : Filter.atTop.IsCoboundedUnder (· ≥ ·) v := hv2.isCoboundedUnder_ge
  have hvliminf : Filter.liminf v Filter.atTop = 0 := hv.liminf_eq
  have hmv : Filter.Tendsto (fun n => -v n) Filter.atTop (nhds 0) := by
    simpa using hv.neg
  have hmv1 : Filter.atTop.IsBoundedUnder (· ≥ ·) (fun n => -v n) := hmv.isBoundedUnder_ge
  have hmv2 : Filter.atTop.IsBoundedUnder (· ≤ ·) (fun n => -v n) := hmv.isBoundedUnder_le
  have hmv1' : Filter.atTop.IsCoboundedUnder (· ≥ ·) (fun n => -v n) := hmv2.isCoboundedUnder_ge
  have hmvliminf : Filter.liminf (fun n => -v n) Filter.atTop = 0 := hmv.liminf_eq
  have huv1 : Filter.atTop.IsBoundedUnder (· ≥ ·) (fun n => u n + v n) :=
    Filter.isBoundedUnder_ge_add hu1 hv1
  have huv2 : Filter.atTop.IsBoundedUnder (· ≤ ·) (fun n => u n + v n) :=
    Filter.isBoundedUnder_le_add hu2 hv2
  apply le_antisymm
  · have h := le_liminf_add (f := Filter.atTop) (u := fun n => u n + v n) (v := fun n => -v n)
      huv1 huv2 hmv1 hmv1'
    have heq : (fun n => u n + v n) + (fun n => -v n) = u := by
      funext n; show (u n + v n) + -v n = u n; ring
    rwa [heq, hmvliminf, add_zero] at h
  · have h := le_liminf_add (f := Filter.atTop) (u := u) (v := v) hu1 hu2 hv1 hv1'
    rwa [hvliminf, add_zero] at h

/-- `A(x) ≤ A(y)` for `x ≤ y`: `posCount A` is monotone in its numeric
argument (as opposed to `posCount_mono`, monotone in the set argument). -/
lemma posCount_mono_arg (A : Set ℕ) {x y : ℕ} (hxy : x ≤ y) : posCount A x ≤ posCount A y := by
  rw [posCount_window_add A hxy]; omega

/-- `A(y) ≤ A(x) + (y - x)` for `x ≤ y`: a window of length `y - x` gains at
most `y - x` elements. Used to bound the "boundary error" terms in Lane's
Theorem 5. -/
lemma posCount_window_le (A : Set ℕ) {x y : ℕ} (hxy : x ≤ y) :
    posCount A y - posCount A x ≤ y - x := by
  rw [posCount_window_add A hxy]
  have h1 : (A ∩ Set.Icc (x + 1) y).ncard ≤ (Set.Icc (x + 1) y).ncard :=
    Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Icc _ _)
  have h2 : (Set.Icc (x + 1) y).ncard = y - x := by
    rw [show Set.Icc (x + 1) y = (↑(Finset.Icc (x + 1) y) : Set ℕ) by simp,
      Set.ncard_coe_finset]
    simp only [Nat.card_Icc]
    omega
  omega

/-- The real-valued form of `posCount_window_le`: `A(y) - A(x) ≤ y - x` with
genuine (non-truncating) real subtraction. -/
lemma posCount_sub_le_real (A : Set ℕ) {x y : ℕ} (hxy : x ≤ y) :
    (posCount A y : ℝ) - posCount A x ≤ (y : ℝ) - x := by
  have h1 := posCount_window_le A hxy
  have h2 := posCount_mono_arg A hxy
  have : (posCount A y - posCount A x : ℝ) ≤ (y - x : ℝ) := by
    rw [← Nat.cast_sub h2, ← Nat.cast_sub hxy]
    exact_mod_cast h1
  linarith

/-- A sequence eventually bounded in absolute value, divided by `n`, tends
to `0`. -/
lemma tendsto_bounded_div_atTop_nhds_zero {u : ℕ → ℝ} {M : ℝ}
    (h : ∀ᶠ y in Filter.atTop, |u y| ≤ M) :
    Filter.Tendsto (fun y : ℕ => u y / y) Filter.atTop (nhds 0) := by
  have hM : 0 ≤ M := by
    obtain ⟨y0, hy0⟩ := h.exists
    exact (abs_nonneg _).trans hy0
  refine squeeze_zero_norm' (a := fun y : ℕ => M / y) ?_ ?_
  · filter_upwards [h] with y hy
    have hyabs : |(y : ℝ)| = (y : ℝ) := abs_of_nonneg (Nat.cast_nonneg y)
    rw [Real.norm_eq_abs, abs_div, hyabs]
    exact div_le_div_of_nonneg_right hy (Nat.cast_nonneg y)
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

end Erdos1112.Proof.Short.KneserDensity
