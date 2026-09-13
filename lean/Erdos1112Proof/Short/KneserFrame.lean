/-
A finite enumeration of the residue classes of `Aseq A B` represented at a
stage `N` where `Bseq A B N` consists of multiples of `g`, and their
(stable) minimum representatives, for the density route documented in
`Short/KneserDensity/README.md`.

Packages `Short/KneserMinima.lean`'s single-stage invariance
(`residues_Aseq_eq_of_multiples`, `classMin_Aseq_eq_of_multiples`) into a
finite frame: `h > 0` classes, an injective-mod-`g` enumeration
`r : Fin h → ℕ` of their minimum representatives with `r ⟨0,_⟩ = 0`, each
`r j` a member of every later `Aseq A B n`, and every element of every
later `Aseq A B n` decomposing as `r j + g * t` for some class index `j`
and some `t : ℕ`. No compression and no density estimate — purely the
finite representative/membership frame `KneserBoundedData.lean` consumes.
-/
import Erdos1112Proof.Short.KneserMinima

namespace Erdos1112.Proof.Short.KneserDensity

open scoped Classical

/-! ### The finite residue set, as a `Finset` -/

/-- The residues mod `g` realized by `A`, as a `Finset ℕ` (well-defined
since every residue lies in `[0, g)`). -/
noncomputable def residueFinset (A : Set ℕ) (g : ℕ) : Finset ℕ :=
  (Finset.range g).filter (fun r => ∃ a ∈ A, a % g = r)

lemma mem_residueFinset {A : Set ℕ} {g r : ℕ} :
    r ∈ residueFinset A g ↔ r < g ∧ ∃ a ∈ A, a % g = r := by
  simp [residueFinset, Finset.mem_filter, Finset.mem_range]

/-- For `g > 0`, `residueFinset A g` (as a set) is exactly `residues A g`:
every residue automatically lies below `g`. -/
lemma coe_residueFinset {A : Set ℕ} {g : ℕ} (hg : 0 < g) :
    (↑(residueFinset A g) : Set ℕ) = residues A g := by
  ext r
  rw [Finset.mem_coe, mem_residueFinset, residues, Set.mem_setOf_eq]
  constructor
  · exact fun h => h.2
  · rintro ⟨a, ha, rfl⟩
    exact ⟨Nat.mod_lt _ hg, a, ha, rfl⟩

/-- The residue-class minimum lands in the class it was taken from, and in
the underlying set: `classMin A g r ∈ A` and `classMin A g r % g = r`,
whenever the class `r` is actually represented in `A`. -/
lemma classMin_mem {A : Set ℕ} {g r : ℕ} (hr : r ∈ residues A g) :
    classMin A g r ∈ A ∧ classMin A g r % g = r := by
  obtain ⟨a, ha, har⟩ := hr
  have hne : {a ∈ A | a % g = r}.Nonempty := ⟨a, ha, har⟩
  exact Nat.sInf_mem hne

/-- The finite residue set of `Aseq A B` is fixed from stage `N` on, once
`Bseq A B N` consists of multiples of `g` (`Finset` form of
`residues_Aseq_eq_of_multiples`). -/
lemma residueFinset_Aseq_eq_of_multiples {g : ℕ} (hg : 0 < g) (A B : Set ℕ) {N : ℕ}
    (hBN : ∀ b ∈ Bseq A B N, g ∣ b) {n : ℕ} (hn : N ≤ n) :
    residueFinset (Aseq A B n) g = residueFinset (Aseq A B N) g := by
  apply Finset.coe_injective
  rw [coe_residueFinset hg, coe_residueFinset hg]
  exact residues_Aseq_eq_of_multiples hg A B hBN n hn

/-- `0` is always a represented residue of `Aseq A B N`, given `0 ∈ A`. -/
lemma zero_mem_residueFinset {A B : Set ℕ} {g : ℕ} (hg : 0 < g) (hA0 : 0 ∈ A) (N : ℕ) :
    0 ∈ residueFinset (Aseq A B N) g :=
  mem_residueFinset.mpr ⟨hg, 0, zero_mem_Aseq hA0 N, Nat.zero_mod g⟩

/-! ### The finite frame -/

/-- **The finite residue/minimum frame (weak-plan step 4).** For `g > 0`,
`0 ∈ A`, and `Bseq A B N` consisting of multiples of `g`: there are `h > 0`
residue classes mod `g` represented in `Aseq A B N`, enumerated by an
injective-mod-`g` `r : Fin h → ℕ` with `r ⟨0,_⟩ = 0`, each `r j` a member of
*every* `Aseq A B n` with `n ≥ N`, and every element of every such
`Aseq A B n` decomposing as `r j + g * t` for some class index `j` and
`t : ℕ`. -/
theorem exists_frame (A B : Set ℕ) (g N : ℕ) (hg : 0 < g) (hA0 : 0 ∈ A)
    (hBN : ∀ b ∈ Bseq A B N, g ∣ b) :
    ∃ (h : ℕ) (hh : 0 < h) (r : Fin h → ℕ),
      r ⟨0, hh⟩ = 0 ∧
      Function.Injective (fun j => r j % g) ∧
      (∀ j (n : ℕ), N ≤ n → r j ∈ Aseq A B n) ∧
      (∀ (n : ℕ), N ≤ n → ∀ a ∈ Aseq A B n, ∃ j t, a = r j + g * t) := by
  set Rfin := residueFinset (Aseq A B N) g with hRfin_def
  have h0mem : 0 ∈ Rfin := zero_mem_residueFinset hg hA0 N
  have hne : Rfin.Nonempty := ⟨0, h0mem⟩
  set h := Rfin.card with hh_def
  have hh : 0 < h := Finset.card_pos.mpr hne
  set ρ := Rfin.orderEmbOfFin (hh_def ▸ rfl : Rfin.card = h) with hρ_def
  have hρ_mem : ∀ j, ρ j ∈ Rfin := fun j => Finset.orderEmbOfFin_mem Rfin _ j
  have hρ_mem_res : ∀ j, ρ j ∈ residues (Aseq A B N) g := fun j =>
    (coe_residueFinset hg) ▸ (Finset.mem_coe.mpr (hρ_mem j))
  have hρ0 : ρ ⟨0, hh⟩ = 0 := by
    rw [hρ_def, Finset.orderEmbOfFin_zero]
    exact le_antisymm (Rfin.min'_le 0 h0mem) (Nat.zero_le _)
  have hρ_surj : ∀ x ∈ Rfin, ∃ j, ρ j = x := by
    intro x hx
    have hxr : x ∈ Set.range ρ := by
      rw [hρ_def, Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr hx
    obtain ⟨j, hj⟩ := hxr
    exact ⟨j, hj⟩
  set r : Fin h → ℕ := fun j => classMin (Aseq A B N) g (ρ j) with hr_def
  have hrmod : ∀ j, r j % g = ρ j := fun j => (classMin_mem (hρ_mem_res j)).2
  have hrmemN : ∀ j, r j ∈ Aseq A B N := fun j => (classMin_mem (hρ_mem_res j)).1
  refine ⟨h, hh, r, ?_, ?_, ?_, ?_⟩
  · -- r ⟨0,hh⟩ = 0
    show classMin (Aseq A B N) g (ρ ⟨0, hh⟩) = 0
    rw [hρ0]
    have h0 : (0 : ℕ) ∈ {a ∈ Aseq A B N | a % g = 0} := ⟨zero_mem_Aseq hA0 N, Nat.zero_mod g⟩
    exact le_antisymm (Nat.sInf_le h0) (Nat.zero_le _)
  · -- injective mod g
    intro i j hij
    have hi : r i % g = ρ i := hrmod i
    have hj : r j % g = ρ j := hrmod j
    have hρeq : ρ i = ρ j := by rw [← hi, ← hj]; exact hij
    exact ρ.injective hρeq
  · -- r j ∈ Aseq A B n for n ≥ N
    intro j n hn
    exact Aseq_monotone A B hn (hrmemN j)
  · -- every element of Aseq A B n (n ≥ N) decomposes as r j + g * t
    intro n hn a ha
    have hresEq : residueFinset (Aseq A B n) g = Rfin :=
      residueFinset_Aseq_eq_of_multiples hg A B hBN hn
    have haRfin : a % g ∈ Rfin := by
      rw [← hresEq]
      exact mem_residueFinset.mpr ⟨Nat.mod_lt _ hg, a, ha, rfl⟩
    obtain ⟨j, hj⟩ := hρ_surj _ haRfin
    have hclassEq : classMin (Aseq A B n) g (ρ j) = r j :=
      classMin_Aseq_eq_of_multiples hg A B hBN (ρ j) n hn
    have haclass : a ∈ {x ∈ Aseq A B n | x % g = ρ j} := ⟨ha, hj.symm⟩
    have hrle : r j ≤ a := by
      rw [← hclassEq]
      exact Nat.sInf_le haclass
    have hmodeq : r j % g = a % g := by rw [hrmod j, hj]
    have hdvd : g ∣ a - r j := (Nat.modEq_iff_dvd' hrle).mp hmodeq
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨j, t, ?_⟩
    omega

end Erdos1112.Proof.Short.KneserDensity
