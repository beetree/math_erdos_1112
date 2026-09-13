/-
Weak Kneser plan (`/tmp/erdos1112-agents/WEAK_KNESER_PLAN.md`), step 2: the
spacing count bound and the *unbounded* minimum-gap density alternative.

If `B` contains `0` and is `f`-spaced (distinct elements at distance `≥ f`),
then `posCount B N ≤ N/f` up to an additive `+1`, giving
`twoFoldLowerDensity A B ≤ lowerDensity A + 1/f`. Consequently, for an
increasing family `A n ⊆ C`, a decreasing family `B n`, constant joint
density `d`, if `B n` is `f`-spaced for arbitrarily large `f`, then
`d ≤ lowerDensity C` (send `f → ∞`). This is one *alternative* of the
dichotomy at step 2 of the plan; the other (`B n` eventually spaced at a
fixed `f`) is a separate worker's task (residue stabilization).
-/
import Mathlib
import Erdos1112Proof.Short.KneserDensity.Defs
import Erdos1112Proof.Short.DensityIteration

namespace Erdos1112.Proof.Short.KneserSpacing

open Erdos1112.Proof.Short.KneserDensity
open Erdos1112.Proof.Short
open Filter

/-- `B` is `f`-spaced: distinct elements of `B` differ by at least `f`. -/
def IsSpaced (B : Set ℕ) (f : ℕ) : Prop :=
  ∀ b1 ∈ B, ∀ b2 ∈ B, b1 < b2 → f ≤ b2 - b1

/-- The "which block of length `f`" map `b ↦ ⌈b/f⌉` is injective on any
`f`-spaced set: two elements `f` apart land in strictly different blocks. -/
lemma spaced_injOn_ceilDiv {B : Set ℕ} {f : ℕ} (hf : 0 < f) (hspaced : IsSpaced B f) :
    Set.InjOn (fun b => (b + f - 1) / f) B := by
  have hshift : ∀ x y : ℕ, x + f ≤ y → (x + f - 1) / f + 1 ≤ (y + f - 1) / f := by
    intro x y hxy
    have h1 : (x + f - 1) + f ≤ (y + f - 1) := by omega
    have h2 : ((x + f - 1) + f) / f = (x + f - 1) / f + 1 := Nat.add_div_right _ hf
    calc (x + f - 1) / f + 1 = ((x + f - 1) + f) / f := h2.symm
      _ ≤ (y + f - 1) / f := Nat.div_le_div_right h1
  intro a ha b hb hab
  dsimp only at hab
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd hab (by
      have hle : a + f ≤ b := by have := hspaced a ha b hb hlt; omega
      have := hshift a b hle
      omega)
  · exact heq
  · exact absurd hab.symm (by
      have hle : b + f ≤ a := by have := hspaced b hb a ha hgt; omega
      have := hshift b a hle
      omega)

/-- **Spacing count bound**: an `f`-spaced set has at most `⌈N/f⌉` positive
elements up to `N`. -/
lemma posCount_le_ceilDiv_of_spaced {B : Set ℕ} {f N : ℕ} (hf : 0 < f)
    (hspaced : IsSpaced B f) :
    posCount B N ≤ (N + f - 1) / f := by
  have hinj : Set.InjOn (fun b => (b + f - 1) / f) (B ∩ Set.Icc 1 N) :=
    (spaced_injOn_ceilDiv hf hspaced).mono Set.inter_subset_left
  have hmaps : ∀ b ∈ B ∩ Set.Icc 1 N, (b + f - 1) / f ∈ Set.Icc 1 ((N + f - 1) / f) := by
    rintro b ⟨-, hb1, hbN⟩
    refine ⟨?_, Nat.div_le_div_right (by omega)⟩
    have : f ≤ b + f - 1 := by omega
    exact Nat.one_le_div_iff hf |>.mpr this
  have hcard := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.finite_Icc _ _)
  have heq : (Set.Icc 1 ((N + f - 1) / f)).ncard = (N + f - 1) / f := by
    rw [show Set.Icc 1 ((N + f - 1) / f) = (↑(Finset.Icc 1 ((N + f - 1) / f)) : Set ℕ) by simp,
      Set.ncard_coe_finset]
    simp
  rwa [heq] at hcard

/-- Real form: `B(N) ≤ N/f + 1`. -/
lemma posCount_le_real_of_spaced {B : Set ℕ} {f N : ℕ} (hf : 0 < f) (hspaced : IsSpaced B f) :
    (posCount B N : ℝ) ≤ (N : ℝ) / f + 1 := by
  have h1 := posCount_le_ceilDiv_of_spaced (B := B) (N := N) hf hspaced
  have h2 : (((N + f - 1) / f : ℕ) : ℝ) ≤ ((N + f - 1 : ℕ) : ℝ) / (f : ℝ) :=
    Nat.cast_div_le (m := N + f - 1) (n := f)
  have h3 : ((N + f - 1 : ℕ) : ℝ) ≤ (N : ℝ) + f := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hEq : N + f - 1 = N - 1 + f := by omega
      rw [hEq]
      push_cast [Nat.cast_sub hN]
      linarith
  have h4 : ((N : ℝ) + f) / f = (N : ℝ) / f + 1 := by
    field_simp
  have hcast : (posCount B N : ℝ) ≤ (((N + f - 1) / f : ℕ) : ℝ) := by exact_mod_cast h1
  calc (posCount B N : ℝ) ≤ (((N + f - 1) / f : ℕ) : ℝ) := hcast
    _ ≤ ((N + f - 1 : ℕ) : ℝ) / f := h2
    _ ≤ ((N : ℝ) + f) / f := by gcongr
    _ = (N : ℝ) / f + 1 := h4

/-- `liminf` is unchanged by adding a constant, for a sequence bounded both
ways. -/
lemma liminf_add_const {u : ℕ → ℝ} (c : ℝ)
    (hu1 : atTop.IsBoundedUnder (· ≥ ·) u) (hu2 : atTop.IsBoundedUnder (· ≤ ·) u) :
    Filter.liminf (fun n => u n + c) atTop = Filter.liminf u atTop + c := by
  have hc1 : atTop.IsBoundedUnder (· ≥ ·) (fun _ : ℕ => c) := isBoundedUnder_const
  have hc2 : atTop.IsBoundedUnder (· ≤ ·) (fun _ : ℕ => c) := isBoundedUnder_const
  have hcneg1 : atTop.IsBoundedUnder (· ≥ ·) (fun _ : ℕ => -c) := isBoundedUnder_const
  have hcneg2 : atTop.IsBoundedUnder (· ≤ ·) (fun _ : ℕ => -c) := isBoundedUnder_const
  have huc1 : atTop.IsBoundedUnder (· ≥ ·) (fun n => u n + c) := Filter.isBoundedUnder_ge_add hu1 hc1
  have huc2 : atTop.IsBoundedUnder (· ≤ ·) (fun n => u n + c) := Filter.isBoundedUnder_le_add hu2 hc2
  apply le_antisymm
  · have h := le_liminf_add (f := atTop) (u := fun n => u n + c) (v := fun _ : ℕ => -c)
      huc1 huc2 hcneg1 hcneg2.isCoboundedUnder_ge
    simp only [liminf_const] at h
    have heq : (fun n => u n + c) + (fun _ : ℕ => -c) = u := by funext n; simp
    rw [heq] at h
    linarith
  · have h := le_liminf_add (f := atTop) (u := u) (v := fun _ : ℕ => c) hu1 hu2 hc1
      hc2.isCoboundedUnder_ge
    simp only [liminf_const] at h
    have heq : u + (fun _ : ℕ => c) = fun n => u n + c := by funext n; simp
    rw [heq] at h
    linarith

/-- `liminf (u + w) = liminf u + L` when `u` is bounded both ways and `w`
converges to `L` (generalizing `liminf_add_of_tendsto_zero` from `L = 0`). -/
lemma liminf_add_of_tendsto {u w : ℕ → ℝ} {L : ℝ}
    (hu1 : atTop.IsBoundedUnder (· ≥ ·) u) (hu2 : atTop.IsBoundedUnder (· ≤ ·) u)
    (hw : Tendsto w atTop (nhds L)) :
    Filter.liminf (fun n => u n + w n) atTop = Filter.liminf u atTop + L := by
  have hw0 : Tendsto (fun n => w n - L) atTop (nhds 0) := by
    have := hw.sub_const L
    simpa using this
  have heq : (fun n => u n + w n) = fun n => (u n + (w n - L)) + L := by
    funext n; ring
  rw [heq, liminf_add_const L (by
      have := hw0.isBoundedUnder_ge
      exact Filter.isBoundedUnder_ge_add hu1 this)
    (by
      have := hw0.isBoundedUnder_le
      exact Filter.isBoundedUnder_le_add hu2 this),
    liminf_add_of_tendsto_zero hu1 hu2 hw0]

/-- **Two-fold density under spacing**: if `B` is `f`-spaced (`f > 0`) then
`δ(A,B) ≤ δ(A) + 1/f`. The `+1` from the count bound vanishes as `N → ∞`. -/
theorem twoFoldLowerDensity_le_add_inv_of_spaced {A B : Set ℕ} {f : ℕ} (hf : 0 < f)
    (hspaced : IsSpaced B f) :
    twoFoldLowerDensity A B ≤ lowerDensity A + 1 / (f : ℝ) := by
  have hBdiv : ∀ N : ℕ, (posCount B N : ℝ) / N ≤ 1 / f + 1 / N := by
    intro N
    have hB := posCount_le_real_of_spaced hf hspaced (N := N)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      have hstep : (posCount B N : ℝ) / N ≤ ((N : ℝ) / f + 1) / N := div_le_div_of_le_nonneg hB
      have hexpand : ((N : ℝ) / f + 1) / N = 1 / f + 1 / N := by
        field_simp
      rwa [hexpand] at hstep
  have hbound : ∀ N : ℕ, ((posCount A N : ℝ) + posCount B N) / N ≤
      (posCount A N : ℝ) / N + (1 / f + 1 / N) := by
    intro N
    have := hBdiv N
    rw [add_div]
    linarith
  have hw : Tendsto (fun N : ℕ => (1 : ℝ) / f + 1 / N) atTop (nhds (1 / f)) := by
    have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using tendsto_const_nhds.add h1
  have heqR : Filter.liminf (fun N : ℕ => (posCount A N : ℝ) / N + (1 / f + 1 / N)) atTop =
      lowerDensity A + 1 / f :=
    liminf_add_of_tendsto (posCountDiv_isBoundedUnder_ge A) (posCountDiv_isBoundedUnder_le A) hw
  have hb1 : atTop.IsBoundedUnder (· ≥ ·) (fun N : ℕ => ((posCount A N : ℝ) + posCount B N) / N) := by
    have hsum := Filter.isBoundedUnder_ge_add (posCountDiv_isBoundedUnder_ge A)
      (posCountDiv_isBoundedUnder_ge B)
    have heq : ((fun N : ℕ => (posCount A N : ℝ) / N) + fun N : ℕ => (posCount B N : ℝ) / N) =
        fun N : ℕ => ((posCount A N : ℝ) + posCount B N) / N := by
      funext N; simp [add_div]
    rwa [heq] at hsum
  have hb2 : atTop.IsCoboundedUnder (· ≥ ·)
      (fun N : ℕ => (posCount A N : ℝ) / N + (1 / f + 1 / N)) :=
    (Filter.isBoundedUnder_le_add (posCountDiv_isBoundedUnder_le A)
      hw.isBoundedUnder_le).isCoboundedUnder_ge
  have hle : twoFoldLowerDensity A B ≤
      Filter.liminf (fun N : ℕ => (posCount A N : ℝ) / N + (1 / f + 1 / N)) atTop := by
    unfold twoFoldLowerDensity
    exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound) hb1 hb2
  rwa [heqR] at hle

/-- **Unbounded minimum-gap density alternative** (weak Kneser plan, step 2):
for an increasing family `A n ⊆ C`, a decreasing family `B n`, with constant
joint density `d`, if `B n` is `f`-spaced for arbitrarily large `f`, then
`d ≤ δ(C)`. Send `f → ∞` in `d = δ(A n, B n) ≤ δ(A n) + 1/f ≤ δ(C) + 1/f`. -/
theorem lowerDensity_le_of_unbounded_spacing
    {A B : ℕ → Set ℕ} {C : Set ℕ} {d : ℝ}
    (hAmono : Monotone A) (hBanti : Antitone B) (hAC : ∀ n, A n ⊆ C)
    (hd : ∀ n, twoFoldLowerDensity (A n) (B n) = d)
    (hspacing : ∀ f : ℕ, 0 < f → ∃ n, IsSpaced (B n) f) :
    d ≤ lowerDensity C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨f, hf⟩ := exists_nat_gt (1 / ε)
  have hf0 : 0 < f := by
    have hfpos : (0 : ℝ) < f := lt_trans (by positivity) hf
    exact_mod_cast hfpos
  obtain ⟨n, hn⟩ := hspacing f hf0
  have hstep := twoFoldLowerDensity_le_add_inv_of_spaced hf0 hn (A := A n)
  rw [hd n] at hstep
  have hmono := lowerDensity_mono (hAC n)
  have hinvf : (1 : ℝ) / f < ε := by
    rw [div_lt_iff₀ (by exact_mod_cast hf0)]
    rw [div_lt_iff₀ hε] at hf
    linarith
  linarith

end Erdos1112.Proof.Short.KneserSpacing
