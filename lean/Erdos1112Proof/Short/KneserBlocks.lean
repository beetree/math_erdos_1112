/- Lane, *A New Approach to Kneser's Theorem on Asymptotic Density* (Ph.D.
dissertation, VPI&SU, 1973), Chapter I, Theorem 13 (pp. 17-20): the
absorbed-block density growth lemma.

This file proves the INNER, already-absorbed version: given `0 ∈ A`,
`0 ∈ B`, `k > 0` and `{0,...,k-1} + B ⊆ A` (the conclusion of Lane's
Theorem 11, proved elsewhere by the e-transform sequence), either `A+B` is
cofinite or `δ(A+B) ≥ k/(k+1) · δ(A,B)`. Theorem 12 (Mann's theorem, finite
form) is taken as an explicit hypothesis (`mann_count`) rather than proved
or postulated here; the composing agent discharges it once
`Short/KneserMann.lean` is ready.

Scope note: Lane's construction picks `x1`, "the smallest element of `B`
which is `≥ x0`" (p. 18). This requires `B` unbounded above; if `B` is
finite and `x0 > max B`, no such `x1` exists. The main theorem below
therefore additionally hypothesizes `B.Infinite`. The finite-`B` case is
NOT handled here; see the report for what remains.

No SHARP table/lift/staircase machinery. -/
import Erdos1112Proof.Short.KneserDensity.Defs

namespace Erdos1112.Proof.Short.KneserDensity

open scoped Pointwise
open scoped Classical

/-! ### Shifted sets and the additive counting identity -/

/-- The "tail from `m`" of a set: `n ∈ shiftSet C m ↔ m + n ∈ C`. This is
Lane's `C̄ = (C - m) ∩ J`, phrased directly as a preimage to avoid `ℕ`
subtraction. -/
def shiftSet (C : Set ℕ) (m : ℕ) : Set ℕ := {n : ℕ | m + n ∈ C}

@[simp] lemma mem_shiftSet {C : Set ℕ} {m n : ℕ} : n ∈ shiftSet C m ↔ m + n ∈ C := Iff.rfl

lemma zero_mem_shiftSet_iff {C : Set ℕ} {m : ℕ} : 0 ∈ shiftSet C m ↔ m ∈ C := by
  simp [shiftSet]

/-- The one-step count jump: `A(n+1) = A(n) + [n+1 ∈ A]`. -/
lemma posCount_succ (A : Set ℕ) (n : ℕ) :
    posCount A (n + 1) = posCount A n + (if n + 1 ∈ A then 1 else 0) := by
  classical
  have hicc : Set.Icc 1 (n + 1) = insert (n + 1) (Set.Icc 1 n) := by
    ext x; simp only [Set.mem_Icc, Set.mem_insert_iff]; omega
  have hfin : (A ∩ Set.Icc 1 n).Finite := (Set.finite_Icc 1 n).inter_of_right _
  by_cases hmem : n + 1 ∈ A
  · have heq : A ∩ Set.Icc 1 (n + 1) = insert (n + 1) (A ∩ Set.Icc 1 n) := by
      rw [hicc, Set.inter_insert_of_mem hmem]
    have hnotmem : (n + 1) ∉ A ∩ Set.Icc 1 n := by
      simp only [Set.mem_inter_iff, Set.mem_Icc]; omega
    unfold posCount
    rw [heq, Set.ncard_insert_of_notMem hnotmem hfin, if_pos hmem]
  · have heq : A ∩ Set.Icc 1 (n + 1) = A ∩ Set.Icc 1 n := by
      rw [hicc, Set.inter_insert_of_notMem hmem]
    unfold posCount
    rw [heq, if_neg hmem, Nat.add_zero]

/-- The additive counting identity for shifted sets: `C(m+x) = C(m) +
C̄(x)` where `C̄ = shiftSet C m`. This is Lane's `Ā(x) = A(x0+x)-A(x0)`
(p. 18), rearranged to avoid `ℕ` subtraction. -/
lemma posCount_add_shiftSet (C : Set ℕ) (m x : ℕ) :
    posCount C (m + x) = posCount C m + posCount (shiftSet C m) x := by
  induction x with
  | zero => simp
  | succ x ih =>
    have h1 : posCount C (m + (x + 1)) = posCount C (m + x) +
        (if (m + x + 1) ∈ C then 1 else 0) := by
      have := posCount_succ C (m + x)
      simpa [Nat.add_assoc] using this
    have h2 : posCount (shiftSet C m) (x + 1) = posCount (shiftSet C m) x +
        (if (x + 1) ∈ shiftSet C m then 1 else 0) := posCount_succ _ x
    have h3 : ((x + 1) ∈ shiftSet C m) ↔ (m + x + 1 ∈ C) := by
      simp [shiftSet, Nat.add_assoc]
    rw [h1, ih, h2]
    by_cases hc : (m + x + 1) ∈ C
    · rw [if_pos hc, if_pos (h3.mpr hc)]; ring
    · have h3' : ¬ (x + 1) ∈ shiftSet C m := fun h => hc (h3.mp h)
      rw [if_neg hc, if_neg h3']
      ring

/-- `k-1`-safe count: if `k` consecutive values from `m` lie in `C` and `x`
reaches the top of that range, `C(x) ≥ k-1` (at most the single value `0`,
if `m = 0`, is excluded from the positive count). -/
lemma posCount_ge_pred_of_range_subset {C : Set ℕ} {m k x : ℕ} (hk : 0 < k)
    (hsub : ∀ j < k, m + j ∈ C) (hx : m + (k - 1) ≤ x) :
    k - 1 ≤ posCount C x := by
  have hIccCard : ∀ a b : ℕ, (Set.Icc a b).ncard = b + 1 - a := fun a b => by
    rw [show Set.Icc a b = (↑(Finset.Icc a b) : Set ℕ) by simp, Set.ncard_coe_finset,
      Nat.card_Icc]
  have hsub' : Set.Icc (max m 1) (m + (k - 1)) ⊆ C ∩ Set.Icc 1 x := by
    intro y hy
    simp only [Set.mem_Icc] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hyj : ∃ j < k, y = m + j := ⟨y - m, by omega, by omega⟩
    obtain ⟨j, hjk, rfl⟩ := hyj
    exact ⟨hsub j hjk, by omega, by omega⟩
  have hcard : (Set.Icc (max m 1) (m + (k - 1))).ncard = m + k - max m 1 := by
    rw [hIccCard]; omega
  have hle : (Set.Icc (max m 1) (m + (k - 1))).ncard ≤ posCount C x :=
    Set.ncard_le_ncard hsub' ((Set.finite_Icc 1 x).inter_of_right _)
  rw [hcard] at hle
  omega

/-! ### Nonnegativity and the growth-to-density step -/

lemma lowerDensity_nonneg (A : Set ℕ) : 0 ≤ lowerDensity A := by
  rw [lowerDensity, Filter.le_liminf_iff
    (isCoboundedUnder_ge_countDiv (C := 1) fun n => by simpa using posCount_le_self A n)
    (isBoundedUnder_ge_countDiv _)]
  intro y hy
  exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le hy (by positivity)

lemma twoFoldLowerDensity_nonneg (A B : Set ℕ) : 0 ≤ twoFoldLowerDensity A B := by
  rw [twoFoldLowerDensity, Filter.le_liminf_iff
    (isCoboundedUnder_ge_div (C := 2) (by norm_num) fun n => by
      have h1 : (posCount A n : ℝ) ≤ n := by exact_mod_cast posCount_le_self A n
      have h2 : (posCount B n : ℝ) ≤ n := by exact_mod_cast posCount_le_self B n
      linarith)
    (isBoundedUnder_ge_div fun n => by positivity)]
  intro y hy
  exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le hy (by positivity)

/-- **Growth to density.** If `C(c) + α(x+1) ≤ 1 + C(c+x)` for all `x` (a
linear growth bound anchored at a fixed point `c`), then `δ(C) ≥ α`. This is
the analytic content behind Lane's final `ε ↓ 0` step (p. 20), phrased so
the fixed anchor `c` absorbs the shift by `x0+x1` for free. -/
lemma growth_to_density {C : Set ℕ} {α : ℝ} {c : ℕ}
    (hbound : ∀ x, (posCount C c : ℝ) + α * (x + 1) ≤ 1 + posCount C (c + x)) :
    α ≤ lowerDensity C := by
  rw [lowerDensity, Filter.le_liminf_iff
    (isCoboundedUnder_ge_countDiv (C := 1) fun n => by simpa using posCount_le_self C n)
    (isBoundedUnder_ge_countDiv _)]
  intro y hy
  rw [Filter.eventually_atTop]
  set δ : ℝ := α - y with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨N1, hN1⟩ := exists_nat_gt ((α * c + 1 - α - posCount C c) / δ)
  refine ⟨max (max c N1) 1, fun n hn => ?_⟩
  have hnc : c ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hbnd := hbound (n - c)
  have hcx : c + (n - c) = n := by omega
  rw [hcx] at hbnd
  have hnN1' : (N1 : ℝ) ≤ n := by exact_mod_cast hnN1
  have hkey : (α * c + 1 - α - posCount C c) / δ < (n : ℝ) := lt_of_lt_of_le hN1 hnN1'
  have hkey2 : α * c + 1 - α - posCount C c < δ * n := by
    rw [div_lt_iff₀ hδpos] at hkey; linarith
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hcast : ((n - c : ℕ) : ℝ) = (n : ℝ) - c := Nat.cast_sub hnc
  rw [hcast] at hbnd
  have hfinal : y * n < (posCount C n : ℝ) := by nlinarith [hbnd]
  exact (lt_div_iff₀ hnpos).mpr hfinal

/-! ### The threshold point `x0` (Lane p. 17: "There exists `x0 ∈ J⁺`...") -/

/-- **Existence of the threshold `x0`.** For `γ` below the two-fold density,
some `x0` is a valid threshold (`γx ≤ A(x)+B(x)` for all `x ≥ x0`), it lies
in `A` (using `B ⊆ A`), and the point just below it (`x0-1` in `ℕ`, which is
`0` again when `x0 = 0` — harmlessly, since the bound is then `0 ≤ 0`) fails
the threshold bound. This is Lane's `x0`, p. 17-18, with the `x0 = 0`
edge case (not addressed by Lane, whose `x0 ∈ J⁺` convention silently
assumes it away) resolved directly: `0 ∈ A` already covers it. -/
lemma exists_threshold {A B : Set ℕ} (hA0 : 0 ∈ A) (hBsubA : B ⊆ A) {γ : ℝ}
    (hγ0 : 0 < γ) (hγlt : γ < twoFoldLowerDensity A B) :
    ∃ x0 : ℕ, x0 ∈ A ∧
      ((posCount A (x0 - 1) : ℝ) + posCount B (x0 - 1) ≤ γ * ((x0 - 1 : ℕ) : ℝ)) ∧
      ∀ x, x0 ≤ x → γ * (x : ℝ) ≤ (posCount A x : ℝ) + posCount B x := by
  classical
  have hbdd : Filter.atTop.IsBoundedUnder (· ≥ ·) (fun n : ℕ => ((posCount A n : ℝ) +
      posCount B n) / n) := isBoundedUnder_ge_div fun n => by positivity
  have hev := Filter.eventually_lt_of_lt_liminf hγlt hbdd
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  set N' := max N 1 with hN'def
  have hvalid : ∀ x, N' ≤ x → γ * (x:ℝ) ≤ (posCount A x : ℝ) + posCount B x := by
    intro x hx
    have hNx : N ≤ x := le_trans (le_max_left _ _) hx
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    have hxpos : (0:ℝ) < x := by exact_mod_cast hx1
    have := hN x hNx
    rw [lt_div_iff₀ hxpos] at this
    linarith
  have hex : ∃ m : ℕ, ∀ x : ℕ, m ≤ x → γ * (x:ℝ) ≤ (posCount A x : ℝ) + posCount B x :=
    ⟨N', hvalid⟩
  set x0 := Nat.find hex with hx0def
  have hthresh := Nat.find_spec hex
  rw [← hx0def] at hthresh
  have hub : (posCount A (x0 - 1) : ℝ) + posCount B (x0 - 1) ≤ γ * ((x0 - 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos x0 with hx00 | hx0pos
    · simp [hx00]
    · have hlt : x0 - 1 < x0 := by omega
      have hfail := Nat.find_min hex hlt
      push_neg at hfail
      obtain ⟨x', hx'ge, hx'lt⟩ := hfail
      have hx'lt0 : x' < x0 := by
        by_contra hge
        push_neg at hge
        exact absurd (hthresh x' hge) (not_le.mpr hx'lt)
      have hx'eq : x' = x0 - 1 := by omega
      rw [hx'eq] at hx'lt
      exact le_of_lt hx'lt
  refine ⟨x0, ?_, hub, hthresh⟩
  rcases Nat.eq_zero_or_pos x0 with hx00 | hx0pos
  · rw [hx00]; exact hA0
  · have hstep : x0 - 1 + 1 = x0 := by omega
    have hjA := posCount_succ A (x0 - 1)
    have hjB := posCount_succ B (x0 - 1)
    rw [hstep] at hjA hjB
    have hge := hthresh x0 le_rfl
    have hcast : ((x0 : ℕ) : ℝ) = ((x0 - 1 : ℕ) : ℝ) + 1 := by
      have h' : ((x0 - 1 + 1 : ℕ) : ℝ) = ((x0 - 1 : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hstep] at h'; exact h'
    rw [hcast] at hge
    have hjA' : (posCount A x0 : ℝ) = posCount A (x0 - 1) +
        (if x0 ∈ A then 1 else 0) := by exact_mod_cast hjA
    have hjB' : (posCount B x0 : ℝ) = posCount B (x0 - 1) +
        (if x0 ∈ B then 1 else 0) := by exact_mod_cast hjB
    rw [hjA', hjB'] at hge
    by_contra hnotA
    have hnotB : x0 ∉ B := fun h => hnotA (hBsubA h)
    rw [if_neg hnotA, if_neg hnotB] at hge
    linarith

/-! ### The shift point `x1` (Lane p. 18: "the smallest element of `B`
which is `≥ x0`") -/

/-- **Existence of `x1`.** Requires `B` unbounded above (see the file
docstring: Lane's construction implicitly needs this). -/
lemma exists_x1 {B : Set ℕ} (hBinf : B.Infinite) (x0 : ℕ) :
    ∃ x1, x1 ∈ B ∧ x0 ≤ x1 ∧ ∀ y, x0 ≤ y → y < x1 → y ∉ B := by
  classical
  have hex : ∃ x1, x1 ∈ B ∧ x0 ≤ x1 := by
    by_cases hx0B : x0 ∈ B
    · exact ⟨x0, hx0B, le_refl x0⟩
    · obtain ⟨b, hbB, hbgt⟩ := hBinf.exists_gt x0
      exact ⟨b, hbB, le_of_lt hbgt⟩
  set x1 := Nat.find hex with hx1def
  have hspec := Nat.find_spec hex
  rw [← hx1def] at hspec
  refine ⟨x1, hspec.1, hspec.2, fun y hy0 hylt hyB => ?_⟩
  exact Nat.find_min hex hylt ⟨hyB, hy0⟩

/-! ### Inequality (I) (Lane p. 18) -/

/-- **Inequality (I).** For `x0 ≥ 1` satisfying the threshold/failure pair
from `exists_threshold`, the count over `(x0-1, x0+x]` beats `γ(x+1)`. -/
lemma ineqI {A B : Set ℕ} {γ : ℝ} {x0 : ℕ} (hx0pos : 1 ≤ x0)
    (hub : (posCount A (x0 - 1) : ℝ) + posCount B (x0 - 1) ≤ γ * ((x0 - 1 : ℕ) : ℝ))
    (hthresh : ∀ x, x0 ≤ x → γ * (x : ℝ) ≤ (posCount A x : ℝ) + posCount B x) (x : ℕ) :
    (posCount A (x0 - 1) : ℝ) + posCount B (x0 - 1) + γ * ((x : ℝ) + 1) ≤
      (posCount A (x0 + x) : ℝ) + posCount B (x0 + x) := by
  have hge := hthresh (x0 + x) (by omega)
  have hcast : γ * ((x0 + x : ℕ) : ℝ) = γ * ((x0 - 1 : ℕ) : ℝ) + γ * ((x : ℝ) + 1) := by
    have h' : ((x0 - 1 + 1 : ℕ) : ℝ) = ((x0 - 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [show x0 - 1 + 1 = x0 from by omega] at h'
    have h2 : ((x0 + x : ℕ) : ℝ) = ((x0 - 1 : ℕ) : ℝ) + ((x : ℝ) + 1) := by
      push_cast; linarith
    rw [h2]; ring
  rw [hcast] at hge
  linarith

/-! ### The `B̄` bound (Lane p. 18, unnumbered inequality before (II)) -/

lemma posCount_mono_index {C : Set ℕ} {n m : ℕ} (h : n ≤ m) : posCount C n ≤ posCount C m :=
  Set.ncard_le_ncard (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc_right h))
    ((Set.finite_Icc 1 m).inter_of_right _)

/-- No `C`-elements in `[a,b]` collapses the count: `C(b) = C(a-1)`. -/
lemma posCount_eq_of_no_mem_Icc {C : Set ℕ} {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : ∀ y, a ≤ y → y ≤ b → y ∉ C) :
    posCount C b = posCount C (a - 1) := by
  have hzero : posCount (shiftSet C (a - 1)) (b - (a - 1)) = 0 := by
    have hempty : shiftSet C (a - 1) ∩ Set.Icc 1 (b - (a - 1)) = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, mem_shiftSet, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hzC, hz1, hz2⟩
      exact hgap (a - 1 + z) (by omega) (by omega) hzC
    unfold posCount
    rw [hempty, Set.ncard_empty]
  have hadd := posCount_add_shiftSet C (a - 1) (b - (a - 1))
  rw [hzero, show a - 1 + (b - (a - 1)) = b from by omega] at hadd
  omega

/-- No `B`-elements in `[x0,x1-1]` collapses the count: `B(x1-1) = B(x0-1)`. -/
lemma posCount_gap {B : Set ℕ} {x0 x1 : ℕ} (hx0pos : 1 ≤ x0) (hx0x1 : x0 ≤ x1)
    (hgap : ∀ y, x0 ≤ y → y < x1 → y ∉ B) :
    posCount B (x1 - 1) = posCount B (x0 - 1) := by
  rcases eq_or_lt_of_le hx0x1 with heq | hlt
  · rw [← heq]
  · exact posCount_eq_of_no_mem_Icc hx0pos (by omega) (fun y hy1 hy2 => hgap y hy1 (by omega))

/-- **`B̄` lower bound.** `B(x0+x) ≤ B(x0-1) + 1 + B̄(x)`, additive form of
Lane's `B̄(x) ≥ B(x0+x)-B(x0-1)-1`. -/
lemma bbar_bound {B : Set ℕ} {x0 x1 : ℕ} (hx0pos : 1 ≤ x0) (hx0x1 : x0 ≤ x1) (hx1B : x1 ∈ B)
    (hgap : ∀ y, x0 ≤ y → y < x1 → y ∉ B) (x : ℕ) :
    posCount B (x0 + x) ≤ posCount B (x0 - 1) + 1 + posCount (shiftSet B x1) x := by
  have h1 : posCount B (x1 + x) = posCount B x1 + posCount (shiftSet B x1) x :=
    posCount_add_shiftSet B x1 x
  have hx1pos : 1 ≤ x1 := le_trans hx0pos hx0x1
  have h2 : posCount B x1 = posCount B (x1 - 1) + 1 := by
    have := posCount_succ B (x1 - 1)
    rw [show x1 - 1 + 1 = x1 from by omega, if_pos hx1B] at this
    exact this
  have h3 : posCount B (x1 - 1) = posCount B (x0 - 1) := posCount_gap hx0pos hx0x1 hgap
  have h4 : posCount B (x0 + x) ≤ posCount B (x1 + x) := posCount_mono_index (by omega)
  omega

/-- **Case one exact fact.** If `x0+x < x1`, no `B`-elements land in
`(x0-1,x0+x]`, so `B(x0+x) = B(x0-1)` exactly. -/
lemma posCount_B_eq_of_lt_x1 {B : Set ℕ} {x0 x1 x : ℕ} (hx0pos : 1 ≤ x0)
    (hgap : ∀ y, x0 ≤ y → y < x1 → y ∉ B) (hxlt : x0 + x < x1) :
    posCount B (x0 + x) = posCount B (x0 - 1) :=
  posCount_eq_of_no_mem_Icc hx0pos (by omega) (fun y hy1 hy2 => hgap y hy1 (by omega))

/-- **Inequality (II)** (Lane p. 18): `1+Ā(x)+B̄(x) ≥ γ(x+1)-1` for all `x`. -/
lemma ineqII {A B : Set ℕ} {γ : ℝ} {x0 x1 : ℕ} (hx0pos : 1 ≤ x0) (hx0A : x0 ∈ A)
    (hx0x1 : x0 ≤ x1) (hx1B : x1 ∈ B) (hgap : ∀ y, x0 ≤ y → y < x1 → y ∉ B)
    (hub : (posCount A (x0 - 1) : ℝ) + posCount B (x0 - 1) ≤ γ * ((x0 - 1 : ℕ) : ℝ))
    (hthresh : ∀ x, x0 ≤ x → γ * (x : ℝ) ≤ (posCount A x : ℝ) + posCount B x) (x : ℕ) :
    γ * ((x : ℝ) + 1) - 1 ≤ 1 + posCount (shiftSet A x0) x + posCount (shiftSet B x1) x := by
  have hI := ineqI hx0pos hub hthresh x
  have hA : posCount A (x0 + x) = posCount A x0 + posCount (shiftSet A x0) x :=
    posCount_add_shiftSet A x0 x
  have hAx0 : posCount A x0 = posCount A (x0 - 1) + 1 := by
    have := posCount_succ A (x0 - 1)
    rw [show x0 - 1 + 1 = x0 from by omega, if_pos hx0A] at this
    exact this
  have hB := bbar_bound hx0pos hx0x1 hx1B hgap x
  have hcastA : (posCount A (x0 + x) : ℝ) = posCount A (x0 - 1) + 1 + posCount (shiftSet A x0) x := by
    exact_mod_cast (by omega : posCount A (x0 + x) = posCount A (x0 - 1) + 1 +
      posCount (shiftSet A x0) x)
  have hcastB : (posCount B (x0 + x) : ℝ) ≤ posCount B (x0 - 1) + 1 + posCount (shiftSet B x1) x := by
    exact_mod_cast hB
  linarith

/-! ### Full-range exact counts, and the k-block landing in `Ā` -/

/-- If `[1,x] ⊆ C` entirely, `C(x) = x` exactly. -/
lemma posCount_eq_of_range {C : Set ℕ} {x : ℕ} (h : ∀ j, 1 ≤ j → j ≤ x → j ∈ C) :
    posCount C x = x := by
  have hsub : Set.Icc 1 x ⊆ C := fun j hj => h j hj.1 hj.2
  unfold posCount
  rw [Set.inter_eq_self_of_subset_right hsub]
  rw [show Set.Icc 1 x = (↑(Finset.Icc 1 x) : Set ℕ) by simp, Set.ncard_coe_finset, Nat.card_Icc]
  omega

/-- The shifted version: if `[d,x] ⊆ C` entirely (`d ≥ 1`), `C(x) = C(d-1) +
(x-d+1)`. This is Lane's "equation III". -/
lemma posCount_eq_add_of_Icc_subset {C : Set ℕ} {d x : ℕ} (hd : 1 ≤ d) (hdx : d ≤ x)
    (hsub : ∀ j, d ≤ j → j ≤ x → j ∈ C) :
    posCount C x = posCount C (d - 1) + (x - d + 1) := by
  have hrange : ∀ j, 1 ≤ j → j ≤ x - d + 1 → j ∈ shiftSet C (d - 1) := by
    intro j hj1 hj2
    show (d - 1) + j ∈ C
    exact hsub ((d - 1) + j) (by omega) (by omega)
  have heq : posCount (shiftSet C (d - 1)) (x - d + 1) = x - d + 1 :=
    posCount_eq_of_range hrange
  have hadd := posCount_add_shiftSet C (d - 1) (x - d + 1)
  rw [heq, show d - 1 + (x - d + 1) = x from by omega] at hadd
  exact hadd

/-- The absorbed `k`-block, shifted, lands entirely in `Ā`: `{x1-x0,...,
x1-x0+k-1} ⊆ shiftSet A x0`, using `{0,...,k-1}+B ⊆ A` at `b := x1`. -/
lemma kblock_in_Abar {A B : Set ℕ} {k x0 x1 : ℕ} (hx0x1 : x0 ≤ x1) (hx1B : x1 ∈ B)
    (habs : ∀ i < k, ∀ b ∈ B, i + b ∈ A) :
    ∀ j < k, (x1 - x0) + j ∈ shiftSet A x0 := by
  intro j hj
  show x0 + ((x1 - x0) + j) ∈ A
  have heq : x0 + ((x1 - x0) + j) = j + x1 := by omega
  rw [heq]
  exact habs j hj x1 hx1B

/-! ### The four cases (Lane p. 19) -/

/-- **Case One** (`x0+x < x1`): the strong bound `γ(x+1) ≤ 1+Ā(x)`, weakened
to the `k/(k+1)` form. -/
lemma case_one {A B : Set ℕ} {γ : ℝ} {k x0 x1 x : ℕ} (hγpos : 0 < γ)
    (hx0pos : 1 ≤ x0) (hx0A : x0 ∈ A)
    (hgap : ∀ y, x0 ≤ y → y < x1 → y ∉ B)
    (hub : (posCount A (x0 - 1) : ℝ) + posCount B (x0 - 1) ≤ γ * ((x0 - 1 : ℕ) : ℝ))
    (hthresh : ∀ x, x0 ≤ x → γ * (x : ℝ) ≤ (posCount A x : ℝ) + posCount B x)
    (hxlt : x0 + x < x1) :
    (k : ℝ) / (k + 1) * γ * ((x : ℝ) + 1) ≤
      1 + posCount (shiftSet A x0) x + posCount (shiftSet B x1) x := by
  have hI := ineqI hx0pos hub hthresh x
  have hBeq := posCount_B_eq_of_lt_x1 hx0pos hgap hxlt
  have hAeq : posCount A (x0 + x) = posCount A (x0 - 1) + 1 + posCount (shiftSet A x0) x := by
    have h1 := posCount_add_shiftSet A x0 x
    have h2 : posCount A x0 = posCount A (x0 - 1) + 1 := by
      have := posCount_succ A (x0 - 1)
      rw [show x0 - 1 + 1 = x0 from by omega, if_pos hx0A] at this
      exact this
    omega
  have hcast : (posCount A (x0 + x) : ℝ) = posCount A (x0 - 1) + 1 +
      posCount (shiftSet A x0) x := by exact_mod_cast hAeq
  have hcastB : (posCount B (x0 + x) : ℝ) = posCount B (x0 - 1) := by exact_mod_cast hBeq
  have hstrong : γ * ((x : ℝ) + 1) ≤ 1 + posCount (shiftSet A x0) x := by linarith
  have hnn : (0:ℝ) ≤ posCount (shiftSet B x1) x := by positivity
  have hk1 : (k:ℝ)/(k+1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0:ℝ) ≤ 1 := by norm_num
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hxnn : (0:ℝ) ≤ γ * ((x:ℝ)+1) := by positivity
  have hweaken : (k:ℝ)/(k+1)*γ*((x:ℝ)+1) ≤ γ*((x:ℝ)+1) := by
    calc (k:ℝ)/(k+1)*γ*((x:ℝ)+1) = (k:ℝ)/(k+1) * (γ*((x:ℝ)+1)) := by ring
      _ ≤ 1 * (γ*((x:ℝ)+1)) := mul_le_mul_of_nonneg_right hk1 hxnn
      _ = γ*((x:ℝ)+1) := by ring
  linarith

/-- **Case Two** (`x1-x0 ≤ x < x1-x0+k`): the absorbed `k`-block, shifted
into `Ā`, covers the gap left by Case One. -/
lemma case_two {A B : Set ℕ} {γ : ℝ} {k x0 x1 x : ℕ} (hγpos : 0 < γ) (hγk1 : γ * k ≤ (k:ℝ) + 1)
    (hx0pos : 1 ≤ x0) (hx0A : x0 ∈ A) (hx0x1 : x0 ≤ x1) (hx1B : x1 ∈ B)
    (hgap : ∀ y, x0 ≤ y → y < x1 → y ∉ B)
    (hub : (posCount A (x0 - 1) : ℝ) + posCount B (x0 - 1) ≤ γ * ((x0 - 1 : ℕ) : ℝ))
    (hthresh : ∀ x, x0 ≤ x → γ * (x : ℝ) ≤ (posCount A x : ℝ) + posCount B x)
    (habs : ∀ i < k, ∀ b ∈ B, i + b ∈ A)
    (hxge : x1 - x0 ≤ x) (hxlt : x < x1 - x0 + k) :
    (k : ℝ) / (k + 1) * γ * ((x : ℝ) + 1) ≤
      1 + posCount (shiftSet A x0) x + posCount (shiftSet B x1) x := by
  set d := x1 - x0 with hddef
  have hkblock := kblock_in_Abar hx0x1 hx1B habs
  rw [← hddef] at hkblock
  have hkg1 : (k:ℝ)/(k+1)*γ ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    linarith
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · have hrange : ∀ j, 1 ≤ j → j ≤ x → j ∈ shiftSet A x0 := by
      intro j hj1 hj2
      have hjk : j < k := by omega
      have hmem := hkblock j hjk
      rwa [hd0, Nat.zero_add] at hmem
    have hAeq : posCount (shiftSet A x0) x = x := posCount_eq_of_range hrange
    have hnn : (0:ℝ) ≤ posCount (shiftSet B x1) x := by positivity
    have hcast : (posCount (shiftSet A x0) x : ℝ) = x := by exact_mod_cast hAeq
    calc (k:ℝ)/(k+1)*γ*((x:ℝ)+1) = ((k:ℝ)/(k+1)*γ)*((x:ℝ)+1) := by ring
      _ ≤ 1*((x:ℝ)+1) := mul_le_mul_of_nonneg_right hkg1 (by positivity)
      _ = (x:ℝ)+1 := by ring
      _ ≤ 1 + posCount (shiftSet A x0) x + posCount (shiftSet B x1) x := by
          rw [hcast]; linarith
  · have hxlt' : x0 + (d - 1) < x1 := by omega
    have hcaseOneAt := case_one (k := k) hγpos hx0pos hx0A hgap hub hthresh hxlt'
    have heqIII : posCount (shiftSet A x0) x =
        posCount (shiftSet A x0) (d - 1) + (x - d + 1) := by
      apply posCount_eq_add_of_Icc_subset hdpos hxge
      intro j hj1 hj2
      have hjk : j - d < k := by omega
      have hmem := hkblock (j - d) hjk
      rwa [show d + (j - d) = j from by omega] at hmem
    have hBmono : posCount (shiftSet B x1) (d - 1) ≤ posCount (shiftSet B x1) x :=
      posCount_mono_index (by omega)
    have hdcast : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
      have : ((d - 1 + 1 : ℕ) : ℝ) = ((d - 1 : ℕ):ℝ) + 1 := by push_cast; ring
      rw [show d - 1 + 1 = d from by omega] at this
      linarith
    rw [hdcast] at hcaseOneAt
    have hxdcast : ((x : ℝ) + 1) = (d : ℝ) + ((x - d + 1 : ℕ) : ℝ) := by
      have hcast1 : ((x - d + 1 : ℕ) : ℝ) = ((x - d : ℕ) : ℝ) + 1 := by push_cast; ring
      have hcast2 : ((x - d : ℕ) : ℝ) = (x : ℝ) - (d : ℝ) := Nat.cast_sub hxge
      rw [hcast1, hcast2]; ring
    have htnn : (0:ℝ) ≤ ((x - d + 1 : ℕ):ℝ) := by positivity
    have hfinal : (k:ℝ)/(k+1)*γ*(d + ((x-d+1:ℕ):ℝ)) ≤
        (k:ℝ)/(k+1)*γ*(d:ℝ) + ((x-d+1:ℕ):ℝ) := by
      have hexp : (k:ℝ)/(k+1)*γ*((d:ℝ) + ((x-d+1:ℕ):ℝ)) =
          (k:ℝ)/(k+1)*γ*(d:ℝ) + ((k:ℝ)/(k+1)*γ)*((x-d+1:ℕ):ℝ) := by ring
      rw [hexp]
      have := mul_le_mul_of_nonneg_right hkg1 htnn
      linarith
    rw [hxdcast]
    have hcastA : (posCount (shiftSet A x0) x : ℝ) = posCount (shiftSet A x0) (d-1) +
        (x - d + 1) := by exact_mod_cast heqIII
    have hcastB : (posCount (shiftSet B x1) (d-1) : ℝ) ≤ posCount (shiftSet B x1) x := by
      exact_mod_cast hBmono
    linarith [hcaseOneAt, hfinal, hcastA, hcastB]

/-- **Case Three** (`x1-x0+k ≤ x`, `γ(x+1) < k+1`): the `k-1`-safe count in
`Ā` alone already beats the target. -/
lemma case_three {A B : Set ℕ} {γ : ℝ} {k x0 x1 x : ℕ} (hk : 0 < k)
    (hx0x1 : x0 ≤ x1) (hx1B : x1 ∈ B) (habs : ∀ i < k, ∀ b ∈ B, i + b ∈ A)
    (hxge : x1 - x0 + k ≤ x) (hxlt : γ * ((x : ℝ) + 1) < (k : ℝ) + 1) :
    (k : ℝ) / (k + 1) * γ * ((x : ℝ) + 1) ≤
      1 + posCount (shiftSet A x0) x + posCount (shiftSet B x1) x := by
  have hkblock := kblock_in_Abar hx0x1 hx1B habs
  have hAge : k - 1 ≤ posCount (shiftSet A x0) x :=
    posCount_ge_pred_of_range_subset hk hkblock (by omega)
  have hcast : ((k - 1 : ℕ) : ℝ) ≤ posCount (shiftSet A x0) x := by exact_mod_cast hAge
  have hk1cast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    have h' : ((k - 1 + 1 : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [show k - 1 + 1 = k from by omega] at h'
    linarith
  have hnn : (0:ℝ) ≤ posCount (shiftSet B x1) x := by positivity
  have hsum : (k:ℝ) ≤ 1 + posCount (shiftSet A x0) x + posCount (shiftSet B x1) x := by linarith
  have hkk1pos : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hweak : (k:ℝ)/(k+1)*γ*((x:ℝ)+1) < (k:ℝ) := by
    calc (k:ℝ)/(k+1)*γ*((x:ℝ)+1) = (k:ℝ)/(k+1) * (γ*((x:ℝ)+1)) := by ring
      _ < (k:ℝ)/(k+1) * ((k:ℝ)+1) := mul_lt_mul_of_pos_left hxlt (by positivity)
      _ = (k:ℝ) := by field_simp
  linarith

/-- **Case Four** (`γ(x+1) ≥ k+1`): inequality (II) alone suffices. -/
lemma case_four {A B : Set ℕ} {γ : ℝ} {k x0 x1 x : ℕ}
    (hx0pos : 1 ≤ x0) (hx0A : x0 ∈ A) (hx0x1 : x0 ≤ x1) (hx1B : x1 ∈ B)
    (hgap : ∀ y, x0 ≤ y → y < x1 → y ∉ B)
    (hub : (posCount A (x0 - 1) : ℝ) + posCount B (x0 - 1) ≤ γ * ((x0 - 1 : ℕ) : ℝ))
    (hthresh : ∀ x, x0 ≤ x → γ * (x : ℝ) ≤ (posCount A x : ℝ) + posCount B x)
    (hxge : (k : ℝ) + 1 ≤ γ * ((x : ℝ) + 1)) :
    (k : ℝ) / (k + 1) * γ * ((x : ℝ) + 1) ≤
      1 + posCount (shiftSet A x0) x + posCount (shiftSet B x1) x := by
  have hII := ineqII hx0pos hx0A hx0x1 hx1B hgap hub hthresh x
  have hkk1pos : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hbound : (k:ℝ)/(k+1)*γ*((x:ℝ)+1) ≤ γ*((x:ℝ)+1) - 1 := by
    rw [show (k:ℝ)/(k+1)*γ*((x:ℝ)+1) = (k:ℝ)*(γ*((x:ℝ)+1))/(k+1) from by ring,
      div_le_iff₀ hkk1pos]
    nlinarith [hxge]
  linarith

/-- **Combined four-case bound.** For every `x`, the `k/(k+1)`-weighted
growth bound holds for `Ā, B̄`, matching the shape needed as `mann_count`'s
hypothesis (with `α := kγ/(k+1)`). -/
lemma four_case_bound {A B : Set ℕ} {γ : ℝ} {k x0 x1 : ℕ} (hk : 0 < k) (hγpos : 0 < γ)
    (hγk1 : γ * k ≤ (k:ℝ) + 1)
    (hx0pos : 1 ≤ x0) (hx0A : x0 ∈ A) (hx0x1 : x0 ≤ x1) (hx1B : x1 ∈ B)
    (hgap : ∀ y, x0 ≤ y → y < x1 → y ∉ B)
    (hub : (posCount A (x0 - 1) : ℝ) + posCount B (x0 - 1) ≤ γ * ((x0 - 1 : ℕ) : ℝ))
    (hthresh : ∀ x, x0 ≤ x → γ * (x : ℝ) ≤ (posCount A x : ℝ) + posCount B x)
    (habs : ∀ i < k, ∀ b ∈ B, i + b ∈ A) (x : ℕ) :
    (k : ℝ) / (k + 1) * γ * ((x : ℝ) + 1) ≤
      1 + posCount (shiftSet A x0) x + posCount (shiftSet B x1) x := by
  by_cases h1 : x0 + x < x1
  · exact case_one hγpos hx0pos hx0A hgap hub hthresh h1
  · push_neg at h1
    by_cases h2 : x < x1 - x0 + k
    · exact case_two hγpos hγk1 hx0pos hx0A hx0x1 hx1B hgap hub hthresh habs (by omega) h2
    · push_neg at h2
      by_cases h3 : γ * ((x : ℝ) + 1) < (k : ℝ) + 1
      · exact case_three hk hx0x1 hx1B habs h2 h3
      · push_neg at h3
        exact case_four hx0pos hx0A hx0x1 hx1B hgap hub hthresh h3

/-! ### Translating `Ā+B̄` back into `A+B` (Lane p. 20) -/

/-- `Ā+B̄`, translated by `x0+x1`, sits inside `A+B` (Lane p. 20: `A+B ⊇
(Ā+x0)+(B̄+x1) = (Ā+B̄)+(x0+x1)`). Only this inclusion is claimed, not
equality: `A+B` may contain sums not coming from the shifted tails. -/
lemma add_shiftSet_subset (A B : Set ℕ) (x0 x1 : ℕ) :
    shiftSet A x0 + shiftSet B x1 ⊆ shiftSet (A + B) (x0 + x1) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  refine ⟨x0 + a, ha, x1 + b, hb, ?_⟩
  show x0 + a + (x1 + b) = x0 + x1 + (a + b)
  ring

/-- If `C(x) = x` exactly, all of `[1,x]` lies in `C` (the converse of
`posCount_eq_of_range`, used for the `mann_count` output at `α = 1`). -/
lemma Icc_subset_of_posCount_eq {C : Set ℕ} {x : ℕ} (h : posCount C x = x) :
    ∀ j, 1 ≤ j → j ≤ x → j ∈ C := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨j, hj1, hj2, hjC⟩ := hcon
  have hssub : C ∩ Set.Icc 1 x ⊂ Set.Icc 1 x := by
    refine Set.ssubset_iff_of_subset Set.inter_subset_right |>.mpr ⟨j, ⟨hj1, hj2⟩, ?_⟩
    simp [hjC]
  have hlt : (C ∩ Set.Icc 1 x).ncard < (Set.Icc 1 x).ncard :=
    Set.ncard_lt_ncard hssub (Set.finite_Icc 1 x)
  have hIccx : (Set.Icc 1 x).ncard = x := by
    rw [show Set.Icc 1 x = (↑(Finset.Icc 1 x) : Set ℕ) by simp, Set.ncard_coe_finset, Nat.card_Icc]
    omega
  unfold posCount at h
  omega

/-! ### Assembly -/

/-- **Shifted growth for `A+B`.** For any valid `γ` (`0 < γ < δ(A,B)`,
`γk ≤ k+1`), some anchor `c` makes the additive growth bound (feeding
`growth_to_density`) hold for `A+B`. Splits on Lane's `x0 = 0` edge case
(direct, `c := 0`, bypassing the shift entirely) vs. the general `x0 ≥ 1`
construction (`c := x0+x1`, the full four-case argument, p. 17-20). -/
lemma shifted_growth {A B : Set ℕ} {k : ℕ} (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) (hk : 0 < k)
    (hBinf : B.Infinite) (habs : ∀ i < k, ∀ b ∈ B, i + b ∈ A)
    (mann_count : ∀ (A B : Set ℕ) (alpha : ℝ) (n : ℕ), 0 ∈ A → 0 ∈ B → 0 < alpha → alpha ≤ 1 →
      (∀ x ≤ n, alpha * ((x : ℝ) + 1) ≤ 1 + (posCount A x : ℝ) + posCount B x) →
      ∀ x ≤ n, alpha * ((x : ℝ) + 1) ≤ 1 + (posCount (A + B) x : ℝ))
    {γ : ℝ} (hγpos : 0 < γ) (hγlt : γ < twoFoldLowerDensity A B) (hγk1 : γ * k ≤ (k:ℝ) + 1) :
    ∃ c : ℕ, ∀ x : ℕ,
      (posCount (A + B) c : ℝ) + (k:ℝ)/(k+1)*γ*((x:ℝ)+1) ≤ 1 + posCount (A + B) (c + x) := by
  have hBsubA : B ⊆ A := fun b hb => by simpa using habs 0 hk b hb
  obtain ⟨x0, hx0A, hub, hthresh⟩ := exists_threshold hA0 hBsubA hγpos hγlt
  set α : ℝ := (k:ℝ)/(k+1)*γ with hαdef
  have hαpos : 0 < α := by rw [hαdef]; positivity
  have hαle : α ≤ 1 := by
    rw [hαdef, div_mul_eq_mul_div, div_le_one (by positivity)]
    linarith
  rcases Nat.eq_zero_or_pos x0 with hx00 | hx0pos
  · refine ⟨0, fun x => ?_⟩
    have hgrowth : ∀ x : ℕ, α * ((x:ℝ)+1) ≤ 1 + (posCount A x : ℝ) + posCount B x := by
      intro x
      have hth := hthresh x (by omega)
      have hstep : α*((x:ℝ)+1) ≤ 1+γ*(x:ℝ) := by
        rw [hαdef, show (k:ℝ)/(k+1)*γ*((x:ℝ)+1) = ((k:ℝ)*γ*((x:ℝ)+1))/((k:ℝ)+1) from by ring,
          div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ)+1)]
        nlinarith [hγk1, Nat.cast_nonneg (α:=ℝ) x, hγpos.le]
      linarith
    have hAB := mann_count A B α x hA0 hB0 hαpos hαle (fun x' _ => hgrowth x') x le_rfl
    simpa using hAB
  · obtain ⟨x1, hx1B, hx0x1, hgap⟩ := exists_x1 hBinf x0
    refine ⟨x0+x1, fun x => ?_⟩
    have hbound := four_case_bound hk hγpos hγk1 hx0pos hx0A hx0x1 hx1B hgap hub hthresh habs
    have hzeroA : (0:ℕ) ∈ shiftSet A x0 := zero_mem_shiftSet_iff.mpr hx0A
    have hzeroB : (0:ℕ) ∈ shiftSet B x1 := zero_mem_shiftSet_iff.mpr hx1B
    have hAB := mann_count (shiftSet A x0) (shiftSet B x1) α x hzeroA hzeroB hαpos hαle
      (fun x' _ => by rw [hαdef]; exact hbound x') x le_rfl
    have hsubset := add_shiftSet_subset A B x0 x1
    have hmono : posCount (shiftSet A x0 + shiftSet B x1) x ≤
        posCount (shiftSet (A+B) (x0+x1)) x := posCount_mono hsubset x
    have hmonocast : (posCount (shiftSet A x0 + shiftSet B x1) x : ℝ) ≤
        posCount (shiftSet (A+B) (x0+x1)) x := by exact_mod_cast hmono
    have hshift := posCount_add_shiftSet (A+B) (x0+x1) x
    have hshiftcast : (posCount (A+B) (x0+x1+x) : ℝ) = posCount (A+B) (x0+x1) +
        posCount (shiftSet (A+B) (x0+x1)) x := by exact_mod_cast hshift
    rw [hαdef] at hAB ⊢
    linarith

/-- The per-`γ` density bound, combining `shifted_growth` with
`growth_to_density`. -/
lemma main_bound {A B : Set ℕ} {k : ℕ} (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) (hk : 0 < k)
    (hBinf : B.Infinite) (habs : ∀ i < k, ∀ b ∈ B, i + b ∈ A)
    (mann_count : ∀ (A B : Set ℕ) (alpha : ℝ) (n : ℕ), 0 ∈ A → 0 ∈ B → 0 < alpha → alpha ≤ 1 →
      (∀ x ≤ n, alpha * ((x : ℝ) + 1) ≤ 1 + (posCount A x : ℝ) + posCount B x) →
      ∀ x ≤ n, alpha * ((x : ℝ) + 1) ≤ 1 + (posCount (A + B) x : ℝ))
    {γ : ℝ} (hγpos : 0 < γ) (hγlt : γ < twoFoldLowerDensity A B) (hγk1 : γ * k ≤ (k:ℝ) + 1) :
    (k:ℝ)/(k+1)*γ ≤ lowerDensity (A+B) := by
  obtain ⟨c, hc⟩ := shifted_growth hA0 hB0 hk hBinf habs mann_count hγpos hγlt hγk1
  exact growth_to_density hc

/-- **Lane, Chapter I, Theorem 13, absorbed-block version.** If `{0,...,k-1}
+ B ⊆ A` (Lane's Theorem 11 conclusion, proved elsewhere), `B` is unbounded
above (see the file docstring), and Theorem 12 (Mann's theorem, finite form)
holds, then either `A+B` is cofinite or `δ(A+B) ≥ k/(k+1) · δ(A,B)`. -/
theorem lane_theorem13_absorbed {A B : Set ℕ} {k : ℕ} (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (hk : 0 < k) (hBinf : B.Infinite) (habs : ∀ i < k, ∀ b ∈ B, i + b ∈ A)
    (mann_count : ∀ (A B : Set ℕ) (alpha : ℝ) (n : ℕ), 0 ∈ A → 0 ∈ B → 0 < alpha → alpha ≤ 1 →
      (∀ x ≤ n, alpha * ((x : ℝ) + 1) ≤ 1 + (posCount A x : ℝ) + posCount B x) →
      ∀ x ≤ n, alpha * ((x : ℝ) + 1) ≤ 1 + (posCount (A + B) x : ℝ)) :
    AsymEq (A + B) Set.univ ∨ lowerDensity (A + B) ≥ (k:ℝ)/(k+1) * twoFoldLowerDensity A B := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  by_cases hcase : (k:ℝ) * twoFoldLowerDensity A B ≤ (k:ℝ) + 1
  · right
    show (k:ℝ)/(k+1) * twoFoldLowerDensity A B ≤ lowerDensity (A+B)
    by_contra hcon
    push_neg at hcon
    set LD := lowerDensity (A+B) with hLDdef
    have hLDnn : 0 ≤ LD := lowerDensity_nonneg (A+B)
    have hLlt : LD * ((k:ℝ)+1)/k < twoFoldLowerDensity A B := by
      rw [div_lt_iff₀ hkpos]
      have hstep : LD*((k:ℝ)+1) < ((k:ℝ)/((k:ℝ)+1)*twoFoldLowerDensity A B)*((k:ℝ)+1) :=
        mul_lt_mul_of_pos_right hcon (by positivity)
      have heq : ((k:ℝ)/((k:ℝ)+1)*twoFoldLowerDensity A B)*((k:ℝ)+1) =
          twoFoldLowerDensity A B * k := by
        field_simp [show ((k:ℝ)+1) ≠ 0 from by positivity]
      linarith [hstep, heq]
    obtain ⟨γ, hγ1, hγ2⟩ := exists_between hLlt
    have hγpos : 0 < γ := lt_of_le_of_lt (by positivity) hγ1
    have hγk1 : γ * k ≤ (k:ℝ) + 1 := le_of_lt (by nlinarith [hγ2, hcase])
    have hmain := main_bound hA0 hB0 hk hBinf habs mann_count hγpos hγ2 hγk1
    have hcontra : LD < (k:ℝ)/(k+1)*γ := by
      have hγ1' : LD*((k:ℝ)+1) < γ*(k:ℝ) := by
        rw [div_lt_iff₀ hkpos] at hγ1; linarith [hγ1]
      rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity : (0:ℝ) < (k:ℝ)+1)]
      nlinarith [hγ1']
    linarith
  · left
    push_neg at hcase
    set γ : ℝ := ((k:ℝ)+1)/k with hγdef
    have hγpos : 0 < γ := by rw [hγdef]; positivity
    have hγlt : γ < twoFoldLowerDensity A B := by
      rw [hγdef, div_lt_iff₀ hkpos]
      linarith
    have hγk1 : γ * k ≤ (k:ℝ) + 1 := by
      rw [hγdef, div_mul_cancel₀]
      exact hkpos.ne'
    obtain ⟨c, hc⟩ := shifted_growth hA0 hB0 hk hBinf habs mann_count hγpos hγlt hγk1
    have hαeq : (k:ℝ)/(k+1)*γ = 1 := by
      rw [hγdef]
      field_simp
    rw [hαeq] at hc
    have heq : ∀ x' : ℕ, posCount (shiftSet (A+B) c) x' = x' := by
      intro x'
      have h1 := hc x'
      have h2 := posCount_add_shiftSet (A+B) c x'
      have h2' : (posCount (A+B) (c+x') : ℝ) = posCount (A+B) c +
          posCount (shiftSet (A+B) c) x' := by exact_mod_cast h2
      have h3 : (x' : ℝ) ≤ posCount (shiftSet (A+B) c) x' := by nlinarith [h1, h2']
      have h4 : posCount (shiftSet (A+B) c) x' ≤ x' := posCount_le_self _ x'
      have h3' : x' ≤ posCount (shiftSet (A+B) c) x' := by exact_mod_cast h3
      omega
    refine ⟨c+1, fun y hy => ?_⟩
    simp only [Set.mem_univ, iff_true]
    obtain ⟨x, rfl⟩ : ∃ x, y = c + x := ⟨y - c, by omega⟩
    have hx1 : 1 ≤ x := by omega
    exact Icc_subset_of_posCount_eq (heq x) x hx1 le_rfl

end Erdos1112.Proof.Short.KneserDensity
