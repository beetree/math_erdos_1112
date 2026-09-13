/-
The tail-covering property — `kA` eventually contains a full
congruence class. Paper: the paper's notation subsection and
the paper's non-existence section.
-/
import Erdos1112Proof.Basic

namespace Erdos1112
namespace Proof

/-- `kA` contains a full congruence-class tail: there are `m ≥ 1`, a *reduced*
residue `ρ < m` (so the class is genuinely infinite), and `X₀` with
`{x ≥ X₀ : x ≡ ρ (mod m)} ⊆ kFoldSumset k a`.

The requirement `ρ < m` is essential: without it the degenerate residue
`ρ = m` covers the empty class and makes the property vacuously true, so the
notion would carry no information. -/
def TailCovering (k : ℕ) (a : ℕ → ℕ) : Prop :=
  ∃ m, 0 < m ∧ ∃ ρ, ρ < m ∧ ∃ X₀, ∀ x, X₀ ≤ x → x % m = ρ → x ∈ kFoldSumset k a

/-- Tail-covering with modulus 1 from "contains all large integers". -/
lemma TailCovering.of_cofinite {k : ℕ} {a : ℕ → ℕ}
    (h : ∃ X₀, ∀ x, X₀ ≤ x → x ∈ kFoldSumset k a) : TailCovering k a := by
  obtain ⟨X₀, hX⟩ := h
  exact ⟨1, one_pos, 0, one_pos, X₀, fun x hx _ => hX x hx⟩

end Proof
end Erdos1112
