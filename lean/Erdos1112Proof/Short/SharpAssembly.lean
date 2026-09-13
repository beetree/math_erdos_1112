import Erdos1112Proof.Short.Funnel
import Erdos1112Proof.Short.Movers
import Erdos1112Proof.Short.EtaEven

namespace Erdos1112.Proof.Short

/-- The paired-mover witness in the uniform triple interface. -/
theorem sharpTriple_of_paired_movers {a b M : ℕ} (ha : 3 ≤ a)
    (hab : a < b) (hbM : b < M) (hco : Nat.Coprime a b)
    (hdvd : a ∣ b + M) : SharpTriple a b M := by
  obtain ⟨r, hr⟩ := hdvd
  obtain ⟨hrun, hcost⟩ := paired_movers ha hab hbM hco (by simpa [mul_comm] using hr)
  refine ⟨(Multiset.replicate (r-1) a + Multiset.replicate ((M-r+1)/2) b) +
    Multiset.replicate ((M-r)/2) M, ?_, ?_, hrun⟩
  · intro x hx
    simp only [Multiset.mem_add, Multiset.mem_replicate] at hx
    rcases hx with (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> simp
  · simpa only [Multiset.card_add, Multiset.card_replicate] using hcost.le

/-- Assemble strong induction. The odd residue branch is an explicit input until
its independent construction has been checked. -/
theorem sharp_all_of_odd
    (hodd : ∀ n b M : ℕ, 1 ≤ n → 2*n+1 < b → b < M →
      Nat.Coprime (2*n+1) b → Nat.Coprime (2*n+1) M → Nat.Coprime b M →
      M+2 ≤ 2*n+1+b → ¬ (2*n+1) ∣ b+M → SharpTriple (2*n+1) b M) :
    ∀ M, SharpAt M := by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    apply sharpAt_of_funnel ih
    intro a b hab hbM hcab hcaM hcbM hdense
    have ha : 3 ≤ a := by omega
    by_cases hdvd : a ∣ b+M
    · exact sharpTriple_of_paired_movers ha hab hbM hcab hdvd
    · rcases Nat.mod_two_eq_zero_or_one a with heven | hoddmod
      · have haeq : a = 2*(a/2) := by omega
        rw [haeq] at hab hcab hcaM hdense hdvd ⊢
        exact eta_even (by omega) hab hbM hcab hcaM hcbM hdense hdvd
      · have haeq : a = 2*(a/2)+1 := by omega
        rw [haeq] at hab hcab hcaM hdense hdvd ⊢
        exact hodd (a/2) b M (by omega) hab hbM hcab hcaM hcbM hdense hdvd

end Erdos1112.Proof.Short
