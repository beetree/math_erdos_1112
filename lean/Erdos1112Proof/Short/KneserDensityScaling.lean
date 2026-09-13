/-
Lane's Chapter Two, Lemma 9, parts (2)-(3): density scaling under the
residue-compression map `Λ` (`Short/KneserCompression.lean`, Definition 6,
Lemma 7). See `Short/KneserDensity/README.md` for the source and page
references.

Lane's Lemma 9 has four parts; this file proves the two that are genuinely
about *density* (parts (2) and (3), plus the single-set analogue of part (2)
that Lane doesn't state separately because his `δ(A,B)` already specializes
to `δ(A)` when `B = {0}`, but which is more convenient to have as its own
statement here):

  δ(A,B) = (h/g) · δ(Â,B̂)          (part 2)
  δ(A) = (h/g) · δ(Â)               (single-set analogue of part 2)

Part (3) (`δ(A+B) = (h/g)·δ(Â+B̂)`, needing `compressedSet_add` reindexed
through a sumset density) and part (1) (`g(B) = (g/h) g(B̂)`, about the
modulus/gcd functions, independent of density) are not proved here.

**Dependency on Lemma 8**: Lane's Lemma 8 says the density liminf, defined
over *all* `n` in `Defs.lean`, can equivalently be computed along the
arithmetic progression `n = x * g` alone. This is proved in
`Short/KneserSubsequence.lean` (`lowerDensity_eq_liminf_along_mul`,
`twoFoldLowerDensity_eq_liminf_along_mul`) and imported directly below.
-/
import Mathlib
import Erdos1112Proof.Short.KneserDensity.Defs
import Erdos1112Proof.Short.KneserCompression
import Erdos1112Proof.Short.KneserSubsequence

namespace Erdos1112.Proof.Short.KneserDensityScaling

open Erdos1112.Proof.Short.KneserDensity
open Erdos1112.Proof.Short.KneserCompression
open Erdos1112.Proof.Short (lowerDensity_eq_liminf_along_mul
  twoFoldLowerDensity_eq_liminf_along_mul)
open Filter

/-! ### Small, self-contained real-analysis lemmas

None of these mention `KneserCompression` or `KneserDensity` at all; they are
generic facts about `liminf` of ratio sequences `(f x : ℝ) / (x * k)`, proved
from scratch because the exact convenience lemmas this file wants either live
under names not present in the pinned Mathlib snapshot (`le_of_forall_pos_le_add`
resolves only for `ENNReal` here, not the general/`ℝ` case a few call sites in
Mathlib itself seem to expect) or are not stated for this denominator shape
(`Defs.lean`'s `isBoundedUnder_ge_countDiv`/`isCoboundedUnder_ge_countDiv` are
for `f n / n`, not `f x / (x * k)`). -/

/-- The real-number fact `(∀ ε > 0, a ≤ b + ε) → a ≤ b`, proved directly
(the general, non-`ENNReal` version of this name does not resolve against the
pinned Mathlib snapshot). -/
private theorem real_le_of_forall_pos_le_add {a b : ℝ} (h : ∀ ε > 0, a ≤ b + ε) : a ≤ b := by
  by_contra hab
  push_neg at hab
  have := h ((a - b) / 2) (by linarith)
  linarith

/-- `C / (x * k) → 0` as `x → ∞`, for fixed `C : ℝ` and `k > 0`. -/
private theorem tendsto_const_div_mul_nhds_zero (C : ℝ) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun x : ℕ => C / (x * k)) atTop (nhds 0) := by
  have hid : ∀ x : ℕ, C / ((x : ℝ) * k) = (C / k) * (1 / x) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have hx0' : (x : ℝ) ≠ 0 := by exact_mod_cast hx0
      have hk0' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp
  simp_rw [hid]
  simpa using (tendsto_const_nhds (x := C / (k : ℝ))).mul tendsto_one_div_atTop_nhds_zero_nat

/-- Pure algebra: `N / (x * g) = (h / g) * (N / (x * h))`, for fixed
`g, h > 0`. This is the pointwise identity that converts a density ratio at
scale `g` into `(h/g)` times the same ratio at scale `h`. -/
private theorem ratio_scale {g h : ℕ} (hg : 0 < g) (hh : 0 < h) (x : ℕ) (N : ℝ) :
    N / ((x : ℝ) * g) = (h : ℝ) / g * (N / ((x : ℝ) * h)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have hx0' : (x : ℝ) ≠ 0 := by exact_mod_cast hx0
    have hg0' : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    have hh0' : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    field_simp

private theorem isBoundedUnder_ge_ratio {k : ℕ} (f : ℕ → ℕ) :
    atTop.IsBoundedUnder (· ≥ ·) (fun x : ℕ => (f x : ℝ) / (x * k)) :=
  ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun x =>
    div_nonneg (Nat.cast_nonneg _) (by positivity))⟩

/-- If `f x ≤ K * (x * m)` for fixed `K, m`, then `f x / (x * k)` is
eventually bounded above (by the constant `K * m / k`, independent of `x`) --
even if `k ≠ m`, since the `x`'s cancel. This lets a single bound on `f`
(stated at whatever scale is natural for `f`) certify boundedness of `f`'s
ratio at *any* other fixed scale, which is exactly what's needed to compare
`liminf`s taken along `x * g` and along `x * h`. -/
private theorem isBoundedUnder_le_ratio {k m : ℕ} (hk : 0 < k) {f : ℕ → ℕ} {K : ℕ}
    (h : ∀ x, f x ≤ K * (x * m)) :
    atTop.IsBoundedUnder (· ≤ ·) (fun x : ℕ => (f x : ℝ) / (x * k)) := by
  refine ⟨(K * m : ℝ) / k, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun x => ?_)⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · simp; positivity
  · have hxk : (0 : ℝ) < (x : ℝ) * k := by positivity
    rw [div_le_div_iff₀ hxk (by exact_mod_cast hk)]
    have h1 : (f x : ℝ) ≤ (K : ℝ) * (x * m) := by exact_mod_cast h x
    calc (f x : ℝ) * k ≤ (K : ℝ) * (x * m) * k := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
      _ = K * m * (x * k) := by ring

private theorem isCoboundedUnder_ge_ratio {k m : ℕ} (hk : 0 < k) {f : ℕ → ℕ} {K : ℕ}
    (h : ∀ x, f x ≤ K * (x * m)) :
    atTop.IsCoboundedUnder (· ≥ ·) (fun x : ℕ => (f x : ℝ) / (x * k)) :=
  (isBoundedUnder_le_ratio hk h).isCoboundedUnder_ge

/-! ### Two abstract `liminf` transport facts

Both proved via `Monotone.map_liminf_of_continuousAt` applied to the
(continuous, monotone) maps `x ↦ c * x` and `x ↦ x + c`. -/

private theorem liminf_const_mul {c : ℝ} (hc : 0 ≤ c) {u : ℕ → ℝ}
    (hcobdd : atTop.IsCoboundedUnder (· ≥ ·) u) (hbdd : atTop.IsBoundedUnder (· ≥ ·) u) :
    c * liminf u atTop = liminf (fun x => c * u x) atTop := by
  have hmono : Monotone (c * ·) := fun a b hab => mul_le_mul_of_nonneg_left hab hc
  have hcont : ContinuousAt (c * ·) (liminf u atTop) :=
    (continuous_const.mul continuous_id).continuousAt
  exact Monotone.map_liminf_of_continuousAt (F := atTop) hmono u hcont hcobdd hbdd

private theorem liminf_add_const {u : ℕ → ℝ} (c : ℝ)
    (hcobdd : atTop.IsCoboundedUnder (· ≥ ·) u) (hbdd : atTop.IsBoundedUnder (· ≥ ·) u) :
    liminf u atTop + c = liminf (fun x => u x + c) atTop := by
  have hmono : Monotone (· + c : ℝ → ℝ) := fun a b hab => by
    simpa using add_le_add_right hab c
  have hcont : ContinuousAt (· + c : ℝ → ℝ) (liminf u atTop) :=
    (continuous_id.add continuous_const).continuousAt
  exact Monotone.map_liminf_of_continuousAt (F := atTop) hmono u hcont hcobdd hbdd

/-- **The sandwich lemma**: if `u x ≤ v x ≤ u x + C / (x * k)` for all `x`
(some fixed `k > 0`, `C ≥ 0`), then `u` and `v` have the same `liminf`. This
is the real-analysis core of Lemma 9: a bounded, `x`-independent numerator
error, divided by a denominator going to infinity, never affects the
`liminf`. Takes both `IsBoundedUnder (≥)` (bounded below) and
`IsBoundedUnder (≤)` (bounded above) for `u` and `v`, since both are needed:
the former for `Filter.liminf_le_liminf`, the latter (via `.isCoboundedUnder_ge`)
to certify cobounded-ness, for `u`/`v` themselves and for the shifted
sequence `u + ε`. -/
private theorem liminf_eq_of_sandwich {u v : ℕ → ℝ} {C : ℝ} {k : ℕ} (hk : 0 < k) (_hC : 0 ≤ C)
    (hle1 : ∀ x, u x ≤ v x) (hle2 : ∀ x, v x ≤ u x + C / (x * k))
    (hbddGe_u : atTop.IsBoundedUnder (· ≥ ·) u) (hbddLe_u : atTop.IsBoundedUnder (· ≤ ·) u)
    (hbddGe_v : atTop.IsBoundedUnder (· ≥ ·) v) (hbddLe_v : atTop.IsBoundedUnder (· ≤ ·) v) :
    liminf v atTop = liminf u atTop := by
  apply le_antisymm
  · apply real_le_of_forall_pos_le_add
    intro ε hε
    have htend := tendsto_const_div_mul_nhds_zero C hk
    have hev : ∀ᶠ x : ℕ in atTop, C / ((x : ℝ) * k) < ε :=
      htend.eventually (eventually_lt_nhds hε)
    have hev' : ∀ᶠ x : ℕ in atTop, v x ≤ u x + ε := by
      filter_upwards [hev] with x hx
      exact (hle2 x).trans (by linarith)
    have hbddLe_uε : atTop.IsBoundedUnder (· ≤ ·) (fun x => u x + ε) := by
      obtain ⟨b, hb⟩ := hbddLe_u
      refine ⟨b + ε, ?_⟩
      rw [Filter.eventually_map] at hb ⊢
      filter_upwards [hb] with x hx
      simpa using add_le_add_right hx ε
    have hcobdd_uε : atTop.IsCoboundedUnder (· ≥ ·) (fun x => u x + ε) :=
      hbddLe_uε.isCoboundedUnder_ge
    calc liminf v atTop ≤ liminf (fun x => u x + ε) atTop :=
          Filter.liminf_le_liminf hev' hbddGe_v hcobdd_uε
      _ = liminf u atTop + ε := (liminf_add_const ε hbddLe_u.isCoboundedUnder_ge hbddGe_u).symm
  · exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hle1) hbddGe_u hbddLe_v.isCoboundedUnder_ge

/-! ### The reusable scaling core

Packages `ratio_scale`, `liminf_const_mul`, and `liminf_eq_of_sandwich` into
one lemma comparing the `liminf` of a count sequence `F` (at scale `g`)
against the `liminf` of a count sequence `Ghat` (at scale `h`) that
sandwiches `F` within a fixed additive constant `C`. Both
`twoFoldLowerDensity_scaling` and `lowerDensity_scaling` below are direct
instances (with `F, Ghat` built from `posCount` sums/singletons, `C = ∑ⱼ r j`
from `KneserCompression.posCount_compressedSet_eq_add_O1`). -/
private theorem density_scale_core {g h : ℕ} (hg : 0 < g) (hh : 0 < h)
    {F Ghat : ℕ → ℕ} {C KF KG : ℕ}
    (hsandwich1 : ∀ x, F x ≤ Ghat x) (hsandwich2 : ∀ x, Ghat x ≤ F x + C)
    (hFbound : ∀ x, F x ≤ KF * (x * g)) (hGbound : ∀ x, Ghat x ≤ KG * (x * h))
    {d1 d2 : ℝ}
    (hd1 : d1 = liminf (fun x : ℕ => (F x : ℝ) / (x * g)) atTop)
    (hd2 : d2 = liminf (fun x : ℕ => (Ghat x : ℝ) / (x * h)) atTop) :
    d1 = (h : ℝ) / g * d2 := by
  have hFbdd_ge_h : atTop.IsBoundedUnder (· ≥ ·) (fun x : ℕ => (F x : ℝ) / (x * h)) :=
    isBoundedUnder_ge_ratio F
  have hFbdd_le_h : atTop.IsBoundedUnder (· ≤ ·) (fun x : ℕ => (F x : ℝ) / (x * h)) :=
    isBoundedUnder_le_ratio hh hFbound
  have hGbdd_ge_h : atTop.IsBoundedUnder (· ≥ ·) (fun x : ℕ => (Ghat x : ℝ) / (x * h)) :=
    isBoundedUnder_ge_ratio Ghat
  have hGbdd_le_h : atTop.IsBoundedUnder (· ≤ ·) (fun x : ℕ => (Ghat x : ℝ) / (x * h)) :=
    isBoundedUnder_le_ratio hh hGbound
  have hstep1 : liminf (fun x : ℕ => (F x : ℝ) / (x * g)) atTop =
      (h : ℝ) / g * liminf (fun x : ℕ => (F x : ℝ) / (x * h)) atTop := by
    have hpt : (fun x : ℕ => (F x : ℝ) / (x * g)) =
        (fun x : ℕ => (h : ℝ) / g * ((F x : ℝ) / (x * h))) := by
      funext x; exact ratio_scale hg hh x (F x : ℝ)
    rw [hpt, ← liminf_const_mul (c := (h : ℝ) / g) (by positivity)
      hFbdd_le_h.isCoboundedUnder_ge hFbdd_ge_h]
  have hstep2 : liminf (fun x : ℕ => (Ghat x : ℝ) / (x * h)) atTop =
      liminf (fun x : ℕ => (F x : ℝ) / (x * h)) atTop := by
    apply liminf_eq_of_sandwich hh (Nat.cast_nonneg C)
      (fun x => by
        have := hsandwich1 x
        exact div_le_div_of_nonneg_right (by exact_mod_cast this) (by positivity))
      (fun x => by
        have := hsandwich2 x
        have h1 : (Ghat x : ℝ) ≤ (F x : ℝ) + C := by exact_mod_cast this
        have h2 : (Ghat x : ℝ) / (x * h) ≤ ((F x : ℝ) + C) / (x * h) :=
          div_le_div_of_nonneg_right h1 (by positivity)
        rcases eq_or_ne x 0 with rfl | hx0
        · simp
        · have hxh : (0 : ℝ) < (x : ℝ) * h := by positivity
          rwa [add_div] at h2)
      hFbdd_ge_h hFbdd_le_h hGbdd_ge_h hGbdd_le_h
  rw [hd1, hd2, hstep1, hstep2]

/-! ### Lane's Lemma 9, part (2), and its single-set analogue

The actual deliverable: given the exact-count facts already proved in
`KneserCompression.lean` (`posCount_compressedSetZero`,
`posCount_compressedSet_eq_add_O1`) and Lane's Lemma 8
(`Short/KneserSubsequence.lean`), the two-fold and single-set
density-scaling identities. -/

/-- **Lane's Lemma 9, part (2)** (p. 30): `δ(A,B) = (h/g) · δ(Â,B̂)`. -/
theorem twoFoldLowerDensity_scaling {g h : ℕ} (hg : 0 < g) (hh : 0 < h) {r : Fin h → ℕ}
    (hr0 : r ⟨0, hh⟩ = 0) (hr_inj : Function.Injective fun j : Fin h => r j % g)
    {A B : Set ℕ} (hA : ∀ a ∈ A, ∃ j t, a = r j + g * t) (hB : ∀ b ∈ B, ∃ t, b = g * t) :
    twoFoldLowerDensity A B =
      (h : ℝ) / g * twoFoldLowerDensity (compressedSet g h r A) (compressedSetZero g h B) := by
  obtain ⟨C, hC⟩ := posCount_compressedSet_eq_add_O1 hg hh hr0 hr_inj hA
  apply density_scale_core hg hh
    (F := fun x => posCount A (x * g) + posCount B (x * g))
    (Ghat := fun x => posCount (compressedSet g h r A) (x * h) +
      posCount (compressedSetZero g h B) (x * h))
    (C := C) (KF := 2) (KG := 2)
  · intro x
    have h1 := (hC x).1
    have h2 := posCount_compressedSetZero hg hh hB x
    omega
  · intro x
    have h1 := (hC x).2
    have h2 := posCount_compressedSetZero hg hh hB x
    omega
  · intro x
    have h1 := posCount_le_self A (x * g)
    have h2 := posCount_le_self B (x * g)
    omega
  · intro x
    have h1 := posCount_le_self (compressedSet g h r A) (x * h)
    have h2 := posCount_le_self (compressedSetZero g h B) (x * h)
    omega
  · have heq : (fun x : ℕ => ((posCount A (x * g) + posCount B (x * g) : ℕ) : ℝ) / (x * g)) =
        (fun x : ℕ => ((posCount A (x * g) : ℝ) + posCount B (x * g)) / (x * g)) := by
      funext x; push_cast; ring
    rw [heq]; exact twoFoldLowerDensity_eq_liminf_along_mul A B hg
  · have heq : (fun x : ℕ => ((posCount (compressedSet g h r A) (x * h) +
          posCount (compressedSetZero g h B) (x * h) : ℕ) : ℝ) / (x * h)) =
        (fun x : ℕ => ((posCount (compressedSet g h r A) (x * h) : ℝ) +
          posCount (compressedSetZero g h B) (x * h)) / (x * h)) := by
      funext x; push_cast; ring
    rw [heq]
    exact twoFoldLowerDensity_eq_liminf_along_mul (compressedSet g h r A)
      (compressedSetZero g h B) hh

/-- **Single-set analogue of Lane's Lemma 9, part (2)**: `δ(A) = (h/g) · δ(Â)`.
Lane does not state this separately (his `δ(A,B)` already specializes to
`δ(A)` when `B = {0}`), but it is more convenient to have on its own. -/
theorem lowerDensity_scaling {g h : ℕ} (hg : 0 < g) (hh : 0 < h) {r : Fin h → ℕ}
    (hr0 : r ⟨0, hh⟩ = 0) (hr_inj : Function.Injective fun j : Fin h => r j % g)
    {A : Set ℕ} (hA : ∀ a ∈ A, ∃ j t, a = r j + g * t) :
    lowerDensity A = (h : ℝ) / g * lowerDensity (compressedSet g h r A) := by
  obtain ⟨C, hC⟩ := posCount_compressedSet_eq_add_O1 hg hh hr0 hr_inj hA
  apply density_scale_core hg hh
    (F := fun x => posCount A (x * g)) (Ghat := fun x => posCount (compressedSet g h r A) (x * h))
    (C := C) (KF := 1) (KG := 1)
  · intro x; exact (hC x).1
  · intro x; exact (hC x).2
  · intro x; simpa using posCount_le_self A (x * g)
  · intro x; simpa using posCount_le_self (compressedSet g h r A) (x * h)
  · exact lowerDensity_eq_liminf_along_mul A hg
  · exact lowerDensity_eq_liminf_along_mul (compressedSet g h r A) hh

end Erdos1112.Proof.Short.KneserDensityScaling
