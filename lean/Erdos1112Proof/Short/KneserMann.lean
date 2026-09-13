/-
Lane's Chapter One, Theorem 12 (the finite Dyson/Mann counting theorem),
proved via Lane's own route: pick a minimal counterexample and derive a
contradiction by constructing a strictly smaller one with the `e`-transform
of Theorem 4 (`Short/KneserDensity/ETransform.lean`). See
`Short/KneserDensity/README.md` for the source and page references.
-/
import Mathlib
import Erdos1112Proof.Short.KneserDensity.Defs
import Erdos1112Proof.Short.KneserDensity.ETransform

namespace Erdos1112.Proof.Short.KneserMann

open Erdos1112.Proof.Short.KneserDensity

/-- `A(x) ≤ A(y)` for `x ≤ y`: index-monotonicity of `posCount`, the
companion to `KneserDensity`'s set-monotonicity `posCount_mono`. -/
lemma posCount_mono_index {A : Set ℕ} {x y : ℕ} (h : x ≤ y) :
    posCount A x ≤ posCount A y := by
  have := posCount_window_add A h
  omega

/-- `|A ∩ [0,k]| = 1 + A(k)`, using `0 ∈ A`: the "extra element at zero"
count used throughout Lane's Theorem 12 proof. -/
lemma posCount_Iic_eq {A : Set ℕ} (hA0 : 0 ∈ A) (k : ℕ) :
    (A ∩ Set.Iic k).ncard = 1 + posCount A k := by
  have hsplit : A ∩ Set.Iic k = insert 0 (A ∩ Set.Icc 1 k) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_insert_iff, Set.mem_Icc]
    constructor
    · rintro ⟨hx, hxk⟩
      rcases Nat.eq_zero_or_pos x with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr ⟨hx, hpos, hxk⟩
    · rintro (rfl | ⟨hx, hpos, hxk⟩)
      · exact ⟨hA0, Nat.zero_le k⟩
      · exact ⟨hx, hxk⟩
  rw [hsplit,
    Set.ncard_insert_of_notMem (by simp) ((Set.finite_Icc 1 k).inter_of_right _)]
  unfold posCount
  omega

/-- The paper's `a*`: the least element of `A` at which the `a*`-transform
genuinely does something (`∃ b ∈ B, a* + b ∉ A`), together with the
minimality that makes it least. -/
def IsAStar (A B : Set ℕ) (a : ℕ) : Prop :=
  a ∈ A ∧ (∃ b ∈ B, a + b ∉ A) ∧ ∀ a' ∈ A, a' < a → ∀ b ∈ B, a' + b ∈ A

/-- `a*` exists whenever `A` is finite (truncated to `[0,n]`), `0 ∈ A`, and
`B` has some positive element: take the least element of the (nonempty,
witnessed by `max A`) failure set. -/
lemma exists_aStar {A B : Set ℕ} {n : ℕ} (hAn : A ⊆ Set.Iic n) (hA0 : 0 ∈ A)
    {b0 : ℕ} (hb0B : b0 ∈ B) (hb0pos : 0 < b0) : ∃ a, IsAStar A B a := by
  have hAf : A.Finite := (Set.finite_Iic n).subset hAn
  have hne : hAf.toFinset.Nonempty := ⟨0, hAf.mem_toFinset.mpr hA0⟩
  set amax := hAf.toFinset.max' hne with hamax_def
  have hamaxA : amax ∈ A := hAf.mem_toFinset.mp (Finset.max'_mem _ hne)
  have hle : ∀ a ∈ A, a ≤ amax := fun a ha => Finset.le_max' _ a (hAf.mem_toFinset.mpr ha)
  have hfail : {a ∈ A | ∃ b ∈ B, a + b ∉ A}.Nonempty := by
    refine ⟨amax, hamaxA, b0, hb0B, fun hmem => ?_⟩
    have := hle _ hmem
    omega
  refine ⟨sInf {a ∈ A | ∃ b ∈ B, a + b ∉ A}, ?_, ?_, ?_⟩
  · exact (Nat.sInf_mem hfail).1
  · exact (Nat.sInf_mem hfail).2
  · intro a' ha' ha'lt b hbB
    by_contra hcon
    have hmem' : a' ∈ {a ∈ A | ∃ b ∈ B, a + b ∉ A} := ⟨ha', b, hbB, hcon⟩
    have := Nat.sInf_le hmem'
    omega

/-- Assertion Two, property I. -/
lemma property_one {A B : Set ℕ} {a : ℕ} (haS : IsAStar A B a) {r : ℕ} (hr : r < a)
    {b : ℕ} (hbB : b ∈ B) {a' : ℕ} (ha'A : a' ∈ A) (ha'r : a' ≤ r) :
    b + a' ∈ A := by
  rw [add_comm]
  exact haS.2.2 a' ha'A (by omega) b hbB

/-- Assertion Two, property II, in additive (subtraction-free) form:
`A(b-1) + 1 + A(r) ≤ A(b+r)` for `b ∈ B` positive and `r < a*`. -/
lemma property_two {A B : Set ℕ} {a : ℕ} (haS : IsAStar A B a) (hA0 : 0 ∈ A)
    {r b : ℕ} (hr : r < a) (hb : 0 < b) (hbB : b ∈ B) :
    posCount A (b - 1) + (1 + posCount A r) ≤ posCount A (b + r) := by
  have hwin := posCount_window_add A (show b - 1 ≤ b + r by omega)
  have hbeq : b - 1 + 1 = b := by omega
  rw [hbeq] at hwin
  have hsub : (A ∩ Set.Iic r).ncard ≤ (A ∩ Set.Icc b (b + r)).ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun a' => b + a')
    · rintro a' ⟨ha'A, ha'r⟩
      simp only [Set.mem_Iic] at ha'r
      refine ⟨property_one haS hr hbB ha'A ha'r, ?_⟩
      simp only [Set.mem_Icc]; omega
    · intro x _ y _ hxy
      simpa using hxy
  rw [posCount_Iic_eq hA0] at hsub
  omega

/-- Assertion Three: on `[0, a*)`, the original bound already holds for `A`
alone (no `B` needed). Proved by taking the least failing `r*`, and
combining `property_two` with `r*`-minimality at the two smaller indices
`b1-1` and `r*-b1`, for any positive `b1 ∈ B` with `b1 ≤ r*`. -/
lemma assertion_three {A B : Set ℕ} {a n : ℕ} (haS : IsAStar A B a) (hA0 : 0 ∈ A)
    {alpha : ℝ}
    (hbound : ∀ x ≤ n, alpha * (x + 1) ≤ 1 + posCount A x + posCount B x)
    (han : a ≤ n) :
    ∀ r < a, alpha * (r + 1) ≤ 1 + posCount A r := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨rstar, hrstar_lt, hrstar_fail⟩ := hcon
  set S : Set ℕ := {r | r < a ∧ alpha * (r + 1) > 1 + posCount A r} with hSdef
  have hSne : S.Nonempty := ⟨rstar, hrstar_lt, hrstar_fail⟩
  set r2 := sInf S with hr2def
  obtain ⟨hr2lt, hr2fail⟩ := Nat.sInf_mem hSne
  have hr2min : ∀ r, r < r2 → ¬ (r < a ∧ alpha * (r + 1) > 1 + posCount A r) := by
    intro r hrlt hmem
    exact absurd (Nat.sInf_le (s := S) hmem) (by omega)
  have hr2n : r2 ≤ n := by omega
  have hb := hbound r2 hr2n
  have hBpos : 0 < posCount B r2 := by
    by_contra hz
    have hz0 : posCount B r2 = 0 := by omega
    rw [hz0] at hb
    push_cast at hb hr2fail
    linarith
  have hBne : (B ∩ Set.Icc 1 r2).Nonempty :=
    (Set.ncard_pos ((Set.finite_Icc 1 r2).inter_of_right _)).mp hBpos
  obtain ⟨b1, hb1B, hb1r⟩ := hBne
  have hb1lo : 1 ≤ b1 := hb1r.1
  have hb1hi : b1 ≤ r2 := hb1r.2
  have hcase_lo : alpha * b1 ≤ 1 + posCount A (b1 - 1) := by
    have hlt : b1 - 1 < r2 := by omega
    have := hr2min (b1 - 1) (by omega)
    have hnf : alpha * ((b1 - 1 : ℕ) + 1) ≤ 1 + posCount A (b1 - 1) := by
      by_contra hc
      exact this ⟨by omega, by push_neg at hc; exact hc⟩
    have heq : ((b1 - 1 : ℕ) : ℝ) + 1 = (b1 : ℝ) := by
      have h1 : (1:ℕ) ≤ b1 := hb1lo
      push_cast [Nat.cast_sub h1]; ring
    rwa [heq] at hnf
  have hcase_mid : alpha * ((r2 - b1 : ℕ) + 1) ≤ 1 + posCount A (r2 - b1) := by
    have hlt : r2 - b1 < r2 := by omega
    have := hr2min (r2 - b1) (by omega)
    by_contra hc
    exact this ⟨by omega, by push_neg at hc; exact hc⟩
  have hstep2 := property_two haS hA0 (a := a) (r := r2 - b1) (b := b1)
    (by omega) hb1lo hb1B
  have hbr : b1 + (r2 - b1) = r2 := by omega
  rw [hbr] at hstep2
  have hcast2 : (posCount A (b1 - 1) : ℝ) + (1 + posCount A (r2 - b1)) ≤ posCount A r2 := by
    exact_mod_cast hstep2
  have hsplit : (b1 : ℝ) + ((r2 - b1 : ℕ) : ℝ) + 1 = (r2 : ℝ) + 1 := by
    have h1 : (b1:ℝ) + ((r2 - b1 : ℕ):ℝ) = (r2:ℝ) := by
      have h2 : b1 ≤ r2 := hb1hi
      push_cast [Nat.cast_sub h2]; ring
    linarith
  have key : alpha * (r2 + 1) ≤ 1 + posCount A r2 := by nlinarith [hcase_lo, hcase_mid, hsplit]
  linarith

/-- Assertion Four: the `a*`-transform strictly decreases `B(n)`, for `a*`
truncated to `B ⊆ Set.Iic n`. -/
lemma assertion_four {A B : Set ℕ} {a n : ℕ} (haS : IsAStar A B a)
    (hBn : B ⊆ Set.Iic n) : posCount (eB A B a) n < posCount B n := by
  obtain ⟨b0, hb0B, hb0fail⟩ := haS.2.1
  have hb0pos : 0 < b0 := by
    rcases Nat.eq_zero_or_pos b0 with h0 | hpos
    · rw [h0, Nat.add_zero] at hb0fail
      exact absurd haS.1 hb0fail
    · exact hpos
  have hb0notB' : b0 ∉ eB A B a := fun h => hb0fail (by rw [add_comm]; exact h.2)
  have hsub : eB A B a ∩ Set.Icc 1 n ⊆ B ∩ Set.Icc 1 n :=
    Set.inter_subset_inter_left _ (eB_subset A B a)
  have hmem : b0 ∈ B ∩ Set.Icc 1 n := ⟨hb0B, hb0pos, hBn hb0B⟩
  have hnotmem : b0 ∉ eB A B a ∩ Set.Icc 1 n := fun h => hb0notB' h.1
  have hfin : (B ∩ Set.Icc 1 n).Finite := (Set.finite_Icc 1 n).inter_of_right _
  have hssub : eB A B a ∩ Set.Icc 1 n ⊂ B ∩ Set.Icc 1 n :=
    (Set.ssubset_iff_of_subset hsub).mpr ⟨b0, hmem, hnotmem⟩
  exact Set.ncard_lt_ncard hssub hfin

/-- The `eA`-transform doesn't change the count exactly at `a` itself: the
only image element that could land in `[1,a]` is `a+0 = a`, already in `A`. -/
lemma posCount_eA_self {A B : Set ℕ} {a : ℕ} (ha : a ∈ A) :
    posCount (eA A B a) a = posCount A a := by
  have heq : eA A B a ∩ Set.Icc 1 a = A ∩ Set.Icc 1 a := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, mem_eA_iff]
    constructor
    · rintro ⟨hx | ⟨b, _, hbe⟩, h1, h2⟩
      · exact ⟨hx, h1, h2⟩
      · have hb0 : b = 0 := by omega
        subst hb0
        rw [Nat.zero_add] at hbe
        subst hbe
        exact ⟨ha, h1, h2⟩
    · rintro ⟨hx, h1, h2⟩
      exact ⟨Or.inl hx, h1, h2⟩
  unfold posCount
  rw [heq]

/-- Lane's identity underlying Assertion Five: for `m ≥ a*`,
`A(m) + B(m-a*) = A'(m) + B'(m-a*)`, derived from Theorem 4 part III
(`posCount_eTransform_eq`) applied at `x = a*`, `y = m`. -/
lemma assertion_five_identity {A B : Set ℕ} {a m : ℕ} (haS : IsAStar A B a) (ham : a ≤ m) :
    posCount A m + posCount B (m - a) = posCount (eA A B a) m + posCount (eB A B a) (m - a) := by
  have hkey := posCount_eTransform_eq (A := A) (B := B) (e := a) (x := a) (y := m) le_rfl ham
  have hself : posCount (eA A B a) a = posCount A a := posCount_eA_self haS.1
  have hm1 : posCount A a ≤ posCount A m := posCount_mono_index ham
  have hm2 : posCount (eA A B a) a ≤ posCount (eA A B a) m := posCount_mono_index ham
  simp only [Nat.sub_self, posCount_zero] at hkey
  omega

/-- If `B` has no element in the window `(k, m]`, then `B(m) = B(k)`. -/
lemma posCount_eq_of_empty_window {B : Set ℕ} {k m : ℕ} (hkm : k ≤ m)
    (hempty : B ∩ Set.Icc (k + 1) m = ∅) : posCount B m = posCount B k := by
  have hwin := posCount_window_add B hkm
  rw [hempty, Set.ncard_empty] at hwin
  omega

/-- The core of Assertion Five, before assembling with the `eA`/`eB`
identity: for `m ≥ a*`, `1 + A(m) + B(m-a*) ≥ α(m+1)`. Splits on whether
`B` has an element forced out of range by the shift (page 19's two cases). -/
lemma assertion_five_core {A B : Set ℕ} {a n : ℕ} (haS : IsAStar A B a) (hA0 : 0 ∈ A)
    {alpha : ℝ} (hbound : ∀ x ≤ n, alpha * (x + 1) ≤ 1 + posCount A x + posCount B x)
    (han : a ≤ n) {m : ℕ} (hm : m ≤ n) (ham : a ≤ m) :
    alpha * (m + 1) ≤ 1 + posCount A m + posCount B (m - a) := by
  by_cases hD : ∃ b ∈ B, b ≤ m ∧ m < a + b
  · obtain ⟨b0, hb0B, hb0m, hb0gt⟩ := hD
    set D : Set ℕ := {b ∈ B | b ≤ m ∧ m < a + b} with hDdef
    have hDne : D.Nonempty := ⟨b0, hb0B, hb0m, hb0gt⟩
    set bstar := sInf D with hbsdef
    obtain ⟨hbsB, hbsm, hbsgt⟩ := Nat.sInf_mem hDne
    have hbspos : 0 < bstar := by omega
    have hbsmin : ∀ b, b < bstar → ¬ (b ∈ B ∧ b ≤ m ∧ m < a + b) := by
      intro b hb hmem
      exact absurd (Nat.sInf_le (s := D) hmem) (by omega)
    set r := m - bstar with hrdef
    have hrlt : r < a := by omega
    have hb1n : bstar - 1 ≤ n := by omega
    have hlo := hbound (bstar - 1) hb1n
    have hmid := assertion_three haS hA0 hbound han r hrlt
    have hstep := property_two haS hA0 (a := a) (r := r) (b := bstar) hrlt hbspos hbsB
    have hbr : bstar + r = m := by omega
    rw [hbr] at hstep
    have hBeq : posCount B (bstar - 1) = posCount B (m - a) := by
      apply posCount_eq_of_empty_window (by omega)
      rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨hbB, hb1, hb2⟩
      exact hbsmin b (by omega) ⟨hbB, by omega, by omega⟩
    have hcast1 : (posCount A (bstar - 1) : ℝ) + 1 + posCount A r ≤ posCount A m := by
      have : (posCount A (bstar - 1) : ℝ) + (1 + posCount A r) ≤ posCount A m := by
        exact_mod_cast hstep
      linarith
    have hcastbr : ((bstar - 1 : ℕ) : ℝ) + 1 = (bstar : ℝ) := by
      have h1 : (1 : ℕ) ≤ bstar := hbspos
      push_cast [Nat.cast_sub h1]; ring
    have hcastm : ((r : ℕ) : ℝ) + 1 + bstar = (m : ℝ) + 1 := by
      have : (bstar : ℝ) + r = m := by exact_mod_cast hbr
      linarith
    have hBcast : (posCount B (bstar - 1) : ℝ) = posCount B (m - a) := by
      exact_mod_cast hBeq
    rw [hcastbr] at hlo
    nlinarith [hlo, hmid, hcast1, hcastm, hBcast]
  · push_neg at hD
    have hBeq : posCount B m = posCount B (m - a) := by
      apply posCount_eq_of_empty_window (show m - a ≤ m by omega)
      rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨hbB, hb1, hb2⟩
      exact absurd (hD b hbB hb2) (by omega)
    have := hbound m hm
    rw [hBeq] at this
    linarith

/-- Assertion Five: the transformed pair `(A', B') = (eA A B a*, eB A B a*)`
still meets the original bound on all of `[0, n]`. -/
lemma assertion_five {A B : Set ℕ} {a n : ℕ} (haS : IsAStar A B a) (hA0 : 0 ∈ A)
    {alpha : ℝ} (hbound : ∀ x ≤ n, alpha * (x + 1) ≤ 1 + posCount A x + posCount B x)
    (han : a ≤ n) :
    ∀ m ≤ n, alpha * (m + 1) ≤ 1 + posCount (eA A B a) m + posCount (eB A B a) m := by
  intro m hm
  by_cases hma : a ≤ m
  · have hcore := assertion_five_core haS hA0 hbound han hm hma
    have hid := assertion_five_identity haS hma
    have hmono : posCount (eB A B a) (m - a) ≤ posCount (eB A B a) m :=
      posCount_mono_index (by omega)
    have hcast : (posCount A m : ℝ) + posCount B (m - a) =
        posCount (eA A B a) m + posCount (eB A B a) (m - a) := by exact_mod_cast hid
    have hmonocast : (posCount (eB A B a) (m - a) : ℝ) ≤ posCount (eB A B a) m := by
      exact_mod_cast hmono
    linarith [hcore, hcast, hmonocast]
  · push_neg at hma
    have h3 := assertion_three haS hA0 hbound han m hma
    have hmonoA : posCount A m ≤ posCount (eA A B a) m := posCount_mono (subset_eA A B a) m
    have hcastA : (posCount A m : ℝ) ≤ posCount (eA A B a) m := by exact_mod_cast hmonoA
    have hnn : (0 : ℝ) ≤ posCount (eB A B a) m := by positivity
    linarith

open scoped Pointwise

/-- Truncating a set to `[0,n]` doesn't change its `posCount` at any
`x ≤ n`, since `Icc 1 x ⊆ Iic n` already. -/
lemma posCount_inter_Iic {A : Set ℕ} {x n : ℕ} (hx : x ≤ n) :
    posCount (A ∩ Set.Iic n) x = posCount A x := by
  unfold posCount
  congr 1
  ext y
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
  constructor
  · rintro ⟨⟨hyA, _⟩, hy1, hy2⟩; exact ⟨hyA, hy1, hy2⟩
  · rintro ⟨hyA, hy1, hy2⟩; exact ⟨⟨hyA, by omega⟩, hy1, hy2⟩

/-- Truncating both summands to `[0,n]` doesn't change `posCount (A+B) n`:
any `a+b ≤ n` with `a,b ≥ 0` already has `a,b ≤ n`. -/
lemma posCount_add_inter_Iic {A B : Set ℕ} {n : ℕ} :
    posCount ((A ∩ Set.Iic n) + (B ∩ Set.Iic n)) n = posCount (A + B) n := by
  unfold posCount
  congr 1
  ext z
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic, Set.mem_add]
  constructor
  · rintro ⟨⟨a, ⟨haA, _⟩, b, ⟨hbB, _⟩, rfl⟩, hz1, hz2⟩
    exact ⟨⟨a, haA, b, hbB, rfl⟩, hz1, hz2⟩
  · rintro ⟨⟨a, haA, b, hbB, rfl⟩, hz1, hz2⟩
    exact ⟨⟨a, ⟨haA, by omega⟩, b, ⟨hbB, by omega⟩, rfl⟩, hz1, hz2⟩

/-- **Theorem 12** (finite Dyson/Mann counting theorem), for sets already
truncated to `[0,n]`. Strong induction on `posCount B n`: the base case
`posCount B n = 0` is direct (`A ⊆ A+B`); otherwise the `a*`-transform
(Assertions One through Five above) produces a strictly smaller
counterexample, contradiction. -/
theorem mann_count_truncated {A B : Set ℕ} {alpha : ℝ} {n : ℕ}
    (hAn : A ⊆ Set.Iic n) (hBn : B ⊆ Set.Iic n)
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (hbound : ∀ x ≤ n, alpha * (x + 1) ≤ 1 + posCount A x + posCount B x) :
    alpha * (n + 1) ≤ 1 + posCount (A + B) n := by
  have key : ∀ k : ℕ, ∀ A B : Set ℕ, A ⊆ Set.Iic n → B ⊆ Set.Iic n → 0 ∈ A → 0 ∈ B →
      posCount B n = k →
      (∀ x ≤ n, alpha * (x + 1) ≤ 1 + posCount A x + posCount B x) →
      alpha * (n + 1) ≤ 1 + posCount (A + B) n := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IH =>
      intro A B hAn hBn hA0 hB0 hBk hbound
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · have hBn0 : posCount B n = 0 := by omega
        have hsub : A ⊆ A + B := fun a ha => Set.mem_add.mpr ⟨a, ha, 0, hB0, by ring⟩
        have hmono : posCount A n ≤ posCount (A + B) n := posCount_mono hsub n
        have hb := hbound n le_rfl
        have hBcast : (posCount B n : ℝ) = 0 := by exact_mod_cast hBn0
        have hcast : (posCount A n : ℝ) ≤ posCount (A + B) n := by exact_mod_cast hmono
        linarith
      · obtain ⟨b0, hb0B, hb0lo, -⟩ :=
          (Set.ncard_pos ((Set.finite_Icc 1 n).inter_of_right B)).mp
            (show 0 < posCount B n by omega)
        obtain ⟨a, haS⟩ := exists_aStar hAn hA0 hb0B hb0lo
        have han : a ≤ n := hAn haS.1
        set A' := eA A B a ∩ Set.Iic n with hA'def
        set B' := eB A B a ∩ Set.Iic n with hB'def
        have hA'sub : A' ⊆ Set.Iic n := Set.inter_subset_right
        have hB'sub : B' ⊆ Set.Iic n := Set.inter_subset_right
        have hA'0 : 0 ∈ A' := ⟨subset_eA A B a hA0, by simp⟩
        have hB'0 : 0 ∈ B' := by
          have h0eB : (0:ℕ) ∈ eB A B a := ⟨hB0, by simpa using haS.1⟩
          exact ⟨h0eB, by simp⟩
        have hbound' : ∀ x ≤ n, alpha * (x + 1) ≤ 1 + posCount A' x + posCount B' x := by
          intro x hx
          have h5 := assertion_five haS hA0 hbound han x hx
          rw [hA'def, hB'def, posCount_inter_Iic hx, posCount_inter_Iic hx]
          exact h5
        have hB'k : posCount B' n < k := by
          have h4 := assertion_four haS hBn
          have heq : posCount B' n = posCount (eB A B a) n := posCount_inter_Iic le_rfl
          omega
        have hIH := IH (posCount B' n) hB'k A' B' hA'sub hB'sub hA'0 hB'0 rfl hbound'
        have hfinal : posCount (A' + B') n ≤ posCount (A + B) n := by
          have heq : posCount (A' + B') n = posCount (eA A B a + eB A B a) n :=
            posCount_add_inter_Iic
          rw [heq]
          exact posCount_mono (add_eA_eB_subset A B a) n
        have hcast : (posCount (A' + B') n : ℝ) ≤ posCount (A + B) n := by exact_mod_cast hfinal
        linarith
  exact key (posCount B n) A B hAn hBn hA0 hB0 rfl hbound

/-- **Theorem 12** (Lane, Chapter I, pp. 13-17): if `A, B ⊆ ℕ` contain `0`
and `1 + A(x) + B(x) ≥ α(x+1)` for every `x ≤ n`, then
`1 + (A+B)(x) ≥ α(x+1)` for every `x ≤ n`. Reduces to `mann_count_truncated`
by truncating both sets to `[0,x]` at each index `x ≤ n` in turn (the
truncation doesn't change any of the counts involved, by
`posCount_inter_Iic`/`posCount_add_inter_Iic`). -/
theorem mann_count {A B : Set ℕ} {alpha : ℝ} {n : ℕ}
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hbound : ∀ x ≤ n, alpha * (x + 1) ≤ 1 + posCount A x + posCount B x) :
    ∀ x ≤ n, alpha * (x + 1) ≤ 1 + posCount (A + B) x := by
  intro x hx
  have hAx : (A ∩ Set.Iic x) ⊆ Set.Iic x := Set.inter_subset_right
  have hBx : (B ∩ Set.Iic x) ⊆ Set.Iic x := Set.inter_subset_right
  have hA0x : 0 ∈ A ∩ Set.Iic x := ⟨hA0, by simp⟩
  have hB0x : 0 ∈ B ∩ Set.Iic x := ⟨hB0, by simp⟩
  have hbound' : ∀ y ≤ x,
      alpha * (y + 1) ≤ 1 + posCount (A ∩ Set.Iic x) y + posCount (B ∩ Set.Iic x) y := by
    intro y hy
    rw [posCount_inter_Iic hy, posCount_inter_Iic hy]
    exact hbound y (hy.trans hx)
  have hmain := mann_count_truncated hAx hBx hA0x hB0x hbound'
  have heq : posCount ((A ∩ Set.Iic x) + (B ∩ Set.Iic x)) x = posCount (A + B) x :=
    posCount_add_inter_Iic
  rwa [heq] at hmain

end Erdos1112.Proof.Short.KneserMann
