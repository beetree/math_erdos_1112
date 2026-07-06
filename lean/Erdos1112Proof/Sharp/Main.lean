/-
Part III, Theorem 3 (SHARP), assembled: strong induction on the maximum M,
reduction to the hard core, and the six-case decision-tree routing
(D / P / L / E / T / B — exhaustive by arithmetic). Paper: proof/03-sharp.md §III.9.
-/
import Erdos1112Proof.Sharp.Graham
import Erdos1112Proof.Sharp.CaseD
import Erdos1112Proof.Sharp.CaseP
import Erdos1112Proof.Sharp.CaseL
import Erdos1112Proof.Sharp.CaseE
import Erdos1112Proof.Sharp.CaseT
import Erdos1112Proof.Sharp.CaseB

namespace Erdos1112
namespace Proof

/-- Hard-core routing: the six cases exhaust the hard core. -/
theorem hardcore_cases {a b M : ℕ} (hc : HardCore a b M) :
    SharpTriple a b M := by
  by_cases hD : a ∣ M
  · exact caseD hc hD
  by_cases hP : a ∣ (b + M)
  · exact caseP hc hP
  by_cases hL : b - a = M - b
  · exact caseL hc hL
  by_cases hμ : M - a ≤ 11
  · exact caseT hc hD hP hL hμ
  by_cases ha : 12 ≤ a
  · exact caseE hc hD hP ha (by omega)
  · exact caseB hc hD hP hL (by omega) (by omega)

/-- **Theorem 3 (SHARP)**, by strong induction on the maximum. -/
theorem sharp (M : ℕ) : SharpAt M := by
  induction M using Nat.strong_induction_on with
  | _ M ih => exact sharpAt_of_hardcore M ih (fun a b hc => hardcore_cases hc)

end Proof
end Erdos1112
