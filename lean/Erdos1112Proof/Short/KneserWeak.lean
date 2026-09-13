/- Kneser’s lower-density/AP-tail consequence, assembled from ordinary
transforms, the minimum-gap dichotomy, and the compressed interval argument.
The source references are recorded in `KneserDensity/README.md`. -/
import Erdos1112Proof.Short.KneserBoundedConclusion
import Erdos1112Proof.Short.KneserFiniteRight
import Erdos1112Proof.Short.KneserSpacing

namespace Erdos1112.Proof.Short.KneserWeak
open Erdos1112.Proof.Short KneserDensity KneserFiniteRight KneserSpacing
open scoped Classical Pointwise

private lemma le_of_forall_lt_add_inv {x y : ℝ} (h : ∀ F : ℕ, 0 < F → x ≤ y + 1 / (F : ℝ)) :
    x ≤ y := by
  by_contra hxy
  push_neg at hxy
  have hxy' : 0 < x - y := by linarith
  obtain ⟨F, hF⟩ := exists_nat_gt (1 / (x - y))
  have hFR0 : (0 : ℝ) < 1 / (x - y) := by positivity
  have hFpos : 0 < F := by exact_mod_cast lt_trans hFR0 hF
  have hFR : (0 : ℝ) < (F : ℝ) := by exact_mod_cast hFpos
  have hinv : 1 / (F : ℝ) < x - y := by
    rw [div_lt_iff₀ hFR]
    rw [div_lt_iff₀ hxy'] at hF
    linarith
  linarith [h F hFpos]

/-! ### Branch 1 (fully proved): unbounded minimum gap in `Bseq A B`
already gives the density alternative, no pending hypothesis. -/

/-- If `Bseq A B n`'s minimum gap is unbounded, `δ(A,B) ≤ δ(A+B)` outright.
Combines, for each large `F`, the spacing/density bound
(`KneserSpacing.twoFoldLowerDensity_le_add_inv_of_spaced`, at the witnessing
`n` with `gapMin (Bseq A B n) ≥ F`) with the joint-density invariance and
sum containment (`KneserConcrete`), then lets `F → ∞`. -/
theorem twoFoldLowerDensity_le_of_unbounded_gapMin
    {A B : Set ℕ} (h0B : 0 ∈ B) (hunb : ∀ M, ∃ n, M ≤ gapMin (Bseq A B n)) :
    twoFoldLowerDensity A B ≤ lowerDensity (A + B) := by
  apply le_of_forall_lt_add_inv
  intro F hF
  obtain ⟨n, hn⟩ := hunb F
  have h0Bn : 0 ∈ Bseq A B n := zero_mem_Bseq h0B n
  have hspaced : IsSpaced (Bseq A B n) F := by
    intro b1 hb1 b2 hb2 hb12
    have hgap := le_gapMin hb1 hb2 hb12
    omega
  have hstep := twoFoldLowerDensity_le_add_inv_of_spaced (A := Aseq A B n) hF hspaced
  have heq : twoFoldLowerDensity A B = twoFoldLowerDensity (Aseq A B n) (Bseq A B n) :=
    (twoFoldLowerDensity_Aseq_Bseq A B n).symm
  have hAsub : Aseq A B n ⊆ A + B := by
    have h1 : Aseq A B n ⊆ Aseq A B n + Bseq A B n := fun a ha => ⟨a, ha, 0, h0Bn, by simp⟩
    exact h1.trans (Aseq_add_Bseq_subset A B n)
  calc twoFoldLowerDensity A B = twoFoldLowerDensity (Aseq A B n) (Bseq A B n) := heq
    _ ≤ lowerDensity (Aseq A B n) + 1 / (F : ℝ) := hstep
    _ ≤ lowerDensity (A + B) + 1 / (F : ℝ) := by
        gcongr
        exact lowerDensity_mono hAsub

/-! ### Branch 2 (fully proved): every `Bseq A B n` is infinite whenever the
density alternative doesn't already hold -/

/-- Failure of the density alternative forces every second component to be
infinite, as required by the interval density estimate. -/
theorem infinite_Bseq_of_not_dens {A B : Set ℕ} (h0B : 0 ∈ B)
    (hfail : ¬ twoFoldLowerDensity A B ≤ lowerDensity (A + B)) :
    ∀ n, (Bseq A B n).Infinite := by
  have hinv : ∀ n, twoFoldLowerDensity (Aseq A B n) (Bseq A B n) = twoFoldLowerDensity A B :=
    twoFoldLowerDensity_Aseq_Bseq A B
  have hsub : ∀ n, Aseq A B n ⊆ A + B := by
    intro n
    have h0Bn : 0 ∈ Bseq A B n := zero_mem_Bseq h0B n
    have h1 : Aseq A B n ⊆ Aseq A B n + Bseq A B n := fun a ha => ⟨a, ha, 0, h0Bn, by simp⟩
    exact h1.trans (Aseq_add_Bseq_subset A B n)
  exact infinite_of_not_le_lowerDensity (A' := Aseq A B) (B' := Bseq A B) hinv hsub hfail

/-- `Bseq A B n` infinite gives a positive element (an infinite set of `ℕ`
cannot be `⊆ {0}`, which is finite). -/
theorem exists_pos_of_infinite_Bseq {A B : Set ℕ} {n : ℕ} (hinf : (Bseq A B n).Infinite) :
    ∃ p ∈ Bseq A B n, 0 < p := by
  by_contra hc
  push_neg at hc
  exact hinf (Set.Finite.subset (Set.finite_singleton 0) (fun p hp => by
    have := hc p hp; simp only [Set.mem_singleton_iff]; omega))

/-- The weak pairwise Kneser law needed for the paper's density shortcut. -/
theorem weak_kneser (A B : Set ℕ) (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) :
    lowerDensity A + lowerDensity B ≤ lowerDensity (A+B) ∨ HasAPTail (A+B) := by
  by_cases hdens : twoFoldLowerDensity A B ≤ lowerDensity (A+B)
  · exact Or.inl ((add_lowerDensity_le_twoFoldLowerDensity A B).trans hdens)
  · have hinf : ∀ n, (Bseq A B n).Infinite := infinite_Bseq_of_not_dens hB0 hdens
    have hanti : ∀ n, Bseq A B (n+1) ⊆ Bseq A B n :=
      fun n => Bseq_antitone A B (Nat.le_succ n)
    have hpos : ∀ n, ∃ p ∈ Bseq A B n, 0 < p :=
      fun n => exists_pos_of_infinite_Bseq (hinf n)
    rcases stabilization_bundle hanti (zero_mem_Bseq hB0) hpos with hunb | hstab
    · exact Or.inl ((add_lowerDensity_le_twoFoldLowerDensity A B).trans
        (twoFoldLowerDensity_le_of_unbounded_gapMin hB0 hunb))
    · obtain ⟨N,f,hf,hstabF,N',hNN',R,hstabR,_⟩ := hstab
      rcases bounded_density_or_tail hA0 hB0 hinf hf hstabF hNN' hstabR with hd | ht
      · exact Or.inl ((add_lowerDensity_le_twoFoldLowerDensity A B).trans hd)
      · exact Or.inr ht

end Erdos1112.Proof.Short.KneserWeak
