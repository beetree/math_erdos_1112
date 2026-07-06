/-
Part III, Lemma 3.2: the frame lemma — residue representatives mod ν plus
padding copies of ν cover a long run. Paper: proof/03-sharp.md §III.1.
-/
import Erdos1112Proof.Sharp.TwoGen

namespace Erdos1112
namespace Proof

/-- **Lemma 3.2 (frame lemma).** If every residue `ρ mod ν` has a
representative `j·g₁ + k·g₂` inside the box `j ≤ Y, k ≤ Z` of height `≤ S`,
and `L − 1 + S ≤ ν·x`, then the multiset `{Y×g₁, Z×g₂, x×ν}` realizes every
integer of `[S, ν·x] ⊇ [S, S+L−1]` as a subset sum. -/
theorem frame_lemma {ν g₁ g₂ Y Z x S : ℕ} (hν : 0 < ν)
    (hreps : ∀ ρ < ν, ∃ j k, j ≤ Y ∧ k ≤ Z ∧
      (j * g₁ + k * g₂) % ν = ρ ∧ j * g₁ + k * g₂ ≤ S) :
    ∀ n, S ≤ n → n ≤ ν * x →
      n ∈ subsetSums (Multiset.replicate Y g₁ + Multiset.replicate Z g₂ +
        Multiset.replicate x ν) := by
  intro n hSn hnx
  obtain ⟨j, k, hjY, hkZ, hmod, hle⟩ := hreps (n % ν) (Nat.mod_lt _ hν)
  set r : ℕ := j * g₁ + k * g₂ with hrdef
  have hrn : r ≤ n := le_trans hle hSn
  have hdvd : ν ∣ n - r := (Nat.modEq_iff_dvd' hrn).mp hmod
  set q : ℕ := (n - r) / ν with hqdef
  have hqν : q * ν = n - r := Nat.div_mul_cancel hdvd
  have hqx : q ≤ x := by
    have h1 : q * ν ≤ x * ν := by
      rw [hqν]
      calc n - r ≤ n := Nat.sub_le _ _
        _ ≤ ν * x := hnx
        _ = x * ν := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right h1 hν
  apply mem_subsetSums.mpr
  refine ⟨Multiset.replicate j g₁ + Multiset.replicate k g₂ +
    Multiset.replicate q ν, ?_, ?_⟩
  · exact add_le_add (add_le_add
      ((Multiset.replicate_le_replicate g₁).mpr hjY)
      ((Multiset.replicate_le_replicate g₂).mpr hkZ))
      ((Multiset.replicate_le_replicate ν).mpr hqx)
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
    calc j * g₁ + k * g₂ + q * ν = r + (n - r) := by rw [← hrdef, hqν]
      _ = n := by omega

end Proof
end Erdos1112
