/- Close the stabilized-gap case by compression and the interval density estimate. -/
import Erdos1112Proof.Short.KneserBoundedData
import Erdos1112Proof.Short.KneserDensityScaling
import Erdos1112Proof.Short.KneserBlockSequence

namespace Erdos1112.Proof.Short
open KneserDensity KneserCompression KneserDensityScaling
open scoped Pointwise

set_option maxHeartbeats 800000 in
theorem bounded_density_or_tail {A B : Set ℕ} (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (hinf : ∀ n, (Bseq A B n).Infinite)
    {N f : ℕ} (hf : 0 < f) (hstabF : ∀ n ≥ N, gapMin (Bseq A B n)=f)
    {N' : ℕ} (hNN' : N ≤ N') {R : Finset ℕ}
    (hstabR : ∀ n ≥ N', residueAlphabet (Bseq A B) f n=R) :
    twoFoldLowerDensity A B ≤ lowerDensity (A+B) ∨ HasAPTail (A+B) := by
  let g := (insert f R).gcd id
  have hg : 0 < g := stable_gcd_pos hf
  have hdvd : ∀ n ≥ N', ∀ b ∈ Bseq A B n, g ∣ b :=
    stable_gcd_dvd_B_from' hf hstabR
  have hBc (n : ℕ) (hn : N' ≤ n) : ∀ b ∈ Bseq A B n, ∃ t, b=g*t := by
    intro b hb
    exact hdvd n hn b hb
  obtain ⟨h,hh,r,hr0,hrinj,hrmem,hrA⟩ := exists_frame A B g N' hg hA0 (hdvd N' le_rfl)
  obtain ⟨_,_,_,hfair,hmono,hanti,_,_,_,_,_,_,hlong⟩ :=
    compressed_grid_bundle hf hstabF hNN' hstabR (g:=g) (F0:=f/g)
      (G:=R.image (·/g)) rfl rfl rfl hh hr0 hrinj
      (fun j => hrmem j N' le_rfl) (hrA N' le_rfl)
  let X := fun n => compressedSet g h r (Aseq A B (N'+n))
  let Y := fun n => compressedSetZero g h (Bseq A B (N'+n))
  let C := Aseq A B N' + Bseq A B N'
  let D := compressedSet g h r C
  let d := twoFoldLowerDensity (X 0) (Y 0)
  have hmX : Monotone X := fun i j hij => hmono (Nat.add_le_add_left hij N')
  have hmY : Antitone Y := fun i j hij => hanti (Nat.add_le_add_left hij N')
  have hfXY : FairAbsorption X Y := hfair.tail N'
  have hY0 (n : ℕ) : 0 ∈ Y n := ⟨0,by simpa using zero_mem_Bseq hB0 (N'+n),by simp⟩
  have hYinf (n : ℕ) : (Y n).Infinite :=
    compressedZero_infinite hh (hinf (N'+n)) (hBc (N'+n) (by omega))
  have hCsub : C ⊆ A+B := Aseq_add_Bseq_subset A B N'
  have hsum (n : ℕ) : X n + Y n ⊆ D := by
    change compressedSet g h r (Aseq A B (N'+n)) +
      compressedSetZero g h (Bseq A B (N'+n)) ⊆ compressedSet g h r C
    rw [← compressedSet_add hg hrinj (hrA (N'+n) (by omega)) (hBc (N'+n) (by omega))]
    apply compressedSet_mono
    exact transformSequence_sum_antitone eStep_sum_subset (A,B) (show N' ≤ N'+n by omega)
  have hscale (n : ℕ) : twoFoldLowerDensity A B = (h:ℝ)/g * twoFoldLowerDensity (X n) (Y n) := by
    rw [← twoFoldLowerDensity_Aseq_Bseq A B (N'+n)]
    exact twoFoldLowerDensity_scaling hg hh hr0 hrinj (hrA (N'+n) (by omega))
      (hBc (N'+n) (by omega))
  have hd (n : ℕ) : twoFoldLowerDensity (X n) (Y n)=d := by
    apply mul_left_cancel₀ (show (h:ℝ)/g ≠ 0 by positivity)
    exact (hscale n).symm.trans (hscale 0)
  have hlong' : ∀ L, ∃ n x, ∀ i < L, x+i ∈ X n := by
    intro L
    obtain ⟨j,hj,x,hx⟩ := hlong L
    refine ⟨j-N',x,?_⟩
    simpa [X,Nat.add_sub_of_le hj] using hx
  rcases block_sequence_dichotomy hmX hmY hfXY hY0 hYinf hsum hd hlong' with hcof | hden
  · right
    apply HasAPTail.mono hCsub
    apply hasAPTail_of_compressed_cofinite hg hh
    obtain ⟨T,hT⟩ := hcof
    exact ⟨T,fun n hn => (hT n hn).2 (Set.mem_univ n)⟩
  · left
    have hCc : ∀ c ∈ C, ∃ j t, c=r j+g*t := by
      rintro c ⟨a,ha,b,hb,rfl⟩
      obtain ⟨j,t,rfl⟩ := hrA N' le_rfl a ha
      obtain ⟨s,rfl⟩ := hBc N' le_rfl b hb
      exact ⟨j,t+s,by ring⟩
    have hsC : lowerDensity C=(h:ℝ)/g * lowerDensity D :=
      lowerDensity_scaling hg hh hr0 hrinj hCc
    apply le_trans _ (lowerDensity_mono hCsub)
    rw [hsC,hscale 0]
    exact mul_le_mul_of_nonneg_left hden (by positivity)

end Erdos1112.Proof.Short
