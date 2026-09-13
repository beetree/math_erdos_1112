/-
Lane's Chapter One, Definition 3 and Theorem 4: the `e`-transformation and
its basic properties. See `Defs.lean` and `Short/KneserDensity/README.md`
for the source and page references.
-/
import Mathlib
import Erdos1112Proof.Short.KneserDensity.Defs

namespace Erdos1112.Proof.Short.KneserDensity

open scoped Pointwise

/-- **`A'`** (Lane, Definition 3, p. 8): `A' = A ∪ (B + e)`. -/
def eA (A B : Set ℕ) (e : ℕ) : Set ℕ := A ∪ (fun b => b + e) '' B

/-- **`B'`** (Lane, Definition 3, p. 8): `B' = B ∩ (A - e)`, phrased
additively as `{b ∈ B : b + e ∈ A}` to avoid `ℕ`-subtraction truncation. -/
def eB (A B : Set ℕ) (e : ℕ) : Set ℕ := B ∩ {b : ℕ | b + e ∈ A}

lemma mem_eA_iff {A B : Set ℕ} {e x : ℕ} : x ∈ eA A B e ↔ x ∈ A ∨ ∃ b ∈ B, b + e = x := by
  simp [eA]

lemma mem_eB_iff {A B : Set ℕ} {e b : ℕ} : b ∈ eB A B e ↔ b ∈ B ∧ b + e ∈ A := Iff.rfl

/-! ### Theorem 4 (p. 8): basic properties of an `e`-transformation -/

/-- Theorem 4, part I (first clause): `A ⊆ A'`. -/
lemma subset_eA (A B : Set ℕ) (e : ℕ) : A ⊆ eA A B e := Set.subset_union_left

/-- Theorem 4, part I (second clause): `B + e ⊆ A'`. -/
lemma image_add_subset_eA (A B : Set ℕ) (e : ℕ) : (fun b => b + e) '' B ⊆ eA A B e :=
  Set.subset_union_right

/-- Theorem 4, part I (third clause): `B' ⊆ B`. -/
lemma eB_subset (A B : Set ℕ) (e : ℕ) : eB A B e ⊆ B := Set.inter_subset_left

/-- Theorem 4, part II: `A' + B' ⊆ A + B`. -/
lemma add_eA_eB_subset (A B : Set ℕ) (e : ℕ) : eA A B e + eB A B e ⊆ A + B := by
  rintro _ ⟨x', hx', y', hy', rfl⟩
  rcases mem_eA_iff.mp hx' with hxA | ⟨b, hb, rfl⟩
  · exact Set.add_mem_add hxA (eB_subset A B e hy')
  · obtain ⟨hyB, hyeA⟩ := hy'
    exact Set.mem_add.mpr ⟨y' + e, hyeA, b, hb, by ring⟩

/-- The key bijection behind Theorem 4, part III (Lane's unnamed
computation on p. 8-9): within the window `(x,y]` (for `e ≤ x ≤ y`), the
elements *gained* by `A'` (over `A`) correspond exactly, via `b ↦ b+e`, to
the elements *lost* by `B'` (from `B`) within the shifted window
`(x-e,y-e]`. Consequently the two window counts agree:
`|A' ∩ (x,y]| + |B' ∩ (x-e,y-e]| = |A ∩ (x,y]| + |B ∩ (x-e,y-e]|`. -/
lemma window_eA_add_window_eB {A B : Set ℕ} {e x y : ℕ} (hex : e ≤ x) (hxy : x ≤ y) :
    (eA A B e ∩ Set.Icc (x + 1) y).ncard + (eB A B e ∩ Set.Icc (x - e + 1) (y - e)).ncard =
      (A ∩ Set.Icc (x + 1) y).ncard + (B ∩ Set.Icc (x - e + 1) (y - e)).ncard := by
  have hAsub : A ∩ Set.Icc (x + 1) y ⊆ eA A B e ∩ Set.Icc (x + 1) y :=
    Set.inter_subset_inter_left _ (subset_eA A B e)
  have hBsub : eB A B e ∩ Set.Icc (x - e + 1) (y - e) ⊆ B ∩ Set.Icc (x - e + 1) (y - e) :=
    Set.inter_subset_inter_left _ (eB_subset A B e)
  have hAfin : (eA A B e ∩ Set.Icc (x + 1) y).Finite := (Set.finite_Icc _ _).inter_of_right _
  have hBfin : (B ∩ Set.Icc (x - e + 1) (y - e)).Finite := (Set.finite_Icc _ _).inter_of_right _
  -- the "gained by `A'`" and "lost by `B'`" sets, and the bijection between them
  have hbij : (eA A B e ∩ Set.Icc (x + 1) y) \ (A ∩ Set.Icc (x + 1) y) =
      (fun b => b + e) '' ((B ∩ Set.Icc (x - e + 1) (y - e)) \ (eB A B e ∩ Set.Icc (x - e + 1) (y - e))) := by
    ext z
    constructor
    · rintro ⟨⟨hzA', hz1, hz2⟩, hnot⟩
      have hzA : z ∉ A := fun h => hnot ⟨h, hz1, hz2⟩
      rcases mem_eA_iff.mp hzA' with hzA'' | ⟨b, hb, rfl⟩
      · exact absurd hzA'' hzA
      · refine ⟨b, ⟨⟨hb, by omega, by omega⟩, ?_⟩, rfl⟩
        exact fun h => hzA h.1.2
    · rintro ⟨b, ⟨⟨hbB, hb1, hb2⟩, hnotB'⟩, rfl⟩
      simp only []
      have hbeA : b + e ∉ A := fun h => hnotB' ⟨⟨hbB, h⟩, hb1, hb2⟩
      refine ⟨⟨mem_eA_iff.mpr (Or.inr ⟨b, hbB, rfl⟩), by omega, by omega⟩, ?_⟩
      exact fun h => hbeA h.1
  have hcard : ((eA A B e ∩ Set.Icc (x + 1) y) \ (A ∩ Set.Icc (x + 1) y)).ncard =
      ((B ∩ Set.Icc (x - e + 1) (y - e)) \ (eB A B e ∩ Set.Icc (x - e + 1) (y - e))).ncard := by
    rw [hbij, Set.ncard_image_of_injective _ (add_left_injective e)]
  have hA' := Set.ncard_diff_add_ncard_of_subset hAsub hAfin
  have hB' := Set.ncard_diff_add_ncard_of_subset hBsub hBfin
  omega

/-- Theorem 4, part III (p. 8): for `y ≥ x ≥ e`,
`A(y) - A(x) + B(y-e) - B(x-e) = A'(y) - A'(x) + B'(y-e) - B'(x-e)`. -/
theorem posCount_eTransform_eq {A B : Set ℕ} {e x y : ℕ} (hex : e ≤ x) (hxy : x ≤ y) :
    posCount A y - posCount A x + (posCount B (y - e) - posCount B (x - e)) =
      posCount (eA A B e) y - posCount (eA A B e) x +
        (posCount (eB A B e) (y - e) - posCount (eB A B e) (x - e)) := by
  have hAw := posCount_window_add A hxy
  have hA'w := posCount_window_add (eA A B e) hxy
  have hxye : x - e ≤ y - e := by omega
  have hBw := posCount_window_add B hxye
  have hB'w := posCount_window_add (eB A B e) hxye
  have hkey := window_eA_add_window_eB (A := A) (B := B) (e := e) hex hxy
  omega

/-! ### Theorem 5 (p. 9-10): `δ(A,B)` is invariant under an `e`-transformation -/

/-- The regrouping step used twice in Lane's proof of Theorem 5 (once for
`A, B` and once, read backwards, for `A', B'`): shifting the second summand
by a fixed `e` changes the two-fold density ratio only by a term that is
bounded and divided by `y → ∞`, hence vanishing in the `liminf`. -/
private lemma liminf_ratio_eq_liminf_shifted (A B : Set ℕ) (e : ℕ) :
    Filter.liminf (fun y : ℕ => ((posCount A y : ℝ) + posCount B y) / y) Filter.atTop =
      Filter.liminf (fun y : ℕ => ((posCount A y : ℝ) - posCount A e + posCount B (y - e)) / y)
        Filter.atTop := by
  set P : ℕ → ℝ := fun n => (posCount A n : ℝ) with hPdef
  set Q : ℕ → ℝ := fun n => (posCount B n : ℝ) with hQdef
  have hsplit : (fun y : ℕ => (P y + Q y) / y) =
      (fun y : ℕ => (P y - P e + Q (y - e)) / y) + fun y : ℕ => (Q y - Q (y - e) + P e) / y := by
    funext y
    show (P y + Q y) / y = (P y - P e + Q (y - e)) / y + (Q y - Q (y - e) + P e) / y
    rw [← add_div]; ring_nf
  have hg1zero : Filter.Tendsto (fun y : ℕ => (Q y - Q (y - e) + P e) / y) Filter.atTop (nhds 0) := by
    apply tendsto_bounded_div_atTop_nhds_zero (M := (e : ℝ) + P e)
    filter_upwards [Filter.eventually_ge_atTop e] with y hy
    have hb := posCount_sub_le_real B (show y - e ≤ y by omega)
    have hb2 : (Q (y - e) : ℝ) ≤ Q y := by
      have h := posCount_mono_arg B (show y - e ≤ y by omega)
      simpa only [hQdef] using (by exact_mod_cast h : (posCount B (y - e) : ℝ) ≤ posCount B y)
    have he : ((y - e : ℕ) : ℝ) = (y : ℝ) - e := Nat.cast_sub hy
    have hPe : (0 : ℝ) ≤ P e := Nat.cast_nonneg _
    rw [abs_of_nonneg (by dsimp only [Q] at hb2 ⊢; linarith)]
    dsimp only [Q] at hb he ⊢
    linarith
  have hu1b1 : Filter.atTop.IsBoundedUnder (· ≥ ·) (fun y : ℕ => (P y - P e + Q (y - e)) / y) := by
    refine ⟨0, Filter.eventually_map.mpr ?_⟩
    filter_upwards [Filter.eventually_ge_atTop e] with y hy
    have hb : P e ≤ P y := by
      have h := posCount_mono_arg A hy
      simpa only [hPdef] using (by exact_mod_cast h : (posCount A e : ℝ) ≤ posCount A y)
    have hQnn : (0 : ℝ) ≤ Q (y - e) := Nat.cast_nonneg _
    exact div_nonneg (by linarith) (Nat.cast_nonneg y)
  have hu1b2 : Filter.atTop.IsBoundedUnder (· ≤ ·) (fun y : ℕ => (P y - P e + Q (y - e)) / y) := by
    refine ⟨2, Filter.eventually_map.mpr ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (max e 1)] with y hy
    have hy1 : 1 ≤ y := le_trans (le_max_right e 1) hy
    have hPe : (0 : ℝ) ≤ P e := Nat.cast_nonneg _
    have hPy : P y ≤ (y : ℝ) := by
      have h := posCount_le_self A y
      simpa only [hPdef] using (by exact_mod_cast h : (posCount A y : ℝ) ≤ y)
    have hQy : Q (y - e) ≤ (y : ℝ) := by
      have h1 := posCount_le_self B (y - e)
      have h2 : y - e ≤ y := Nat.sub_le y e
      have h3 : (posCount B (y - e) : ℝ) ≤ ((y - e : ℕ) : ℝ) := by exact_mod_cast h1
      have h4 : ((y - e : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast h2
      simpa only [hQdef] using h3.trans h4
    rw [div_le_iff₀ (show (0 : ℝ) < y by exact_mod_cast hy1)]
    nlinarith
  rw [hsplit]
  exact liminf_add_of_tendsto_zero hu1b1 hu1b2 hg1zero

/-- **Theorem 5** (p. 9-10): an `e`-transformation preserves the two-fold
lower density `δ(A,B)`. -/
theorem twoFoldLowerDensity_eTransform_eq (A B : Set ℕ) (e : ℕ) :
    twoFoldLowerDensity A B = twoFoldLowerDensity (eA A B e) (eB A B e) := by
  set P : ℕ → ℝ := fun n => (posCount A n : ℝ) with hPdef
  set Q : ℕ → ℝ := fun n => (posCount B n : ℝ) with hQdef
  set P' : ℕ → ℝ := fun n => (posCount (eA A B e) n : ℝ) with hP'def
  set Q' : ℕ → ℝ := fun n => (posCount (eB A B e) n : ℝ) with hQ'def
  have hstep1 := liminf_ratio_eq_liminf_shifted A B e
  have hstep3 := liminf_ratio_eq_liminf_shifted (eA A B e) (eB A B e) e
  have hstep2 : (fun y : ℕ => (P y - P e + Q (y - e)) / y) =ᶠ[Filter.atTop]
      (fun y : ℕ => (P' y - P' e + Q' (y - e)) / y) := by
    filter_upwards [Filter.eventually_ge_atTop e] with y hy
    have h := posCount_eTransform_eq (A := A) (B := B) (e := e) (le_refl e) hy
    simp only [Nat.sub_self, posCount_zero, Nat.sub_zero] at h
    have hA : posCount A e ≤ posCount A y := posCount_mono_arg A hy
    have hA' : posCount (eA A B e) e ≤ posCount (eA A B e) y := posCount_mono_arg (eA A B e) hy
    have hcast : (posCount A y - posCount A e + posCount B (y - e) : ℝ) =
        (posCount (eA A B e) y - posCount (eA A B e) e + posCount (eB A B e) (y - e) : ℝ) := by
      exact_mod_cast h
    show (P y - P e + Q (y - e)) / y = (P' y - P' e + Q' (y - e)) / y
    simp only [hPdef, hQdef, hP'def, hQ'def]
    rw [hcast]
  unfold twoFoldLowerDensity
  show Filter.liminf (fun y : ℕ => (P y + Q y) / y) Filter.atTop =
      Filter.liminf (fun y : ℕ => (P' y + Q' y) / y) Filter.atTop
  rw [hstep1, Filter.liminf_congr hstep2, ← hstep3]

end Erdos1112.Proof.Short.KneserDensity
