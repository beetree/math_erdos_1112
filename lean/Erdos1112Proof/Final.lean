/-
The three target theorems of Erdős Problem #1112, stated identically to the
statement file `Erdos1112.lean` (`erdos_1112`, `erdos_1112_existence_bound`,
`erdos_1112_strong_nonexistence`) and proved here from the development in
namespace `Erdos1112.Proof`. These are the canonical `Erdos1112.*` results;
`Erdos1112.lean` carries their definitions, this file carries their proofs.
-/
import Erdos1112Proof.Existence.Nested
import Erdos1112Proof.NonEx.Main

namespace Erdos1112

/-- Existence half with the paper's explicit ratio bound: when
`d₂ ≥ k + 1`, the concrete ratio `192 · d₂` works. -/
theorem erdos_1112_existence_bound (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (hd : d₁ < d₂) (h : k + 1 ≤ d₂) :
    RatioWorks k d₁ d₂ (192 * d₂) :=
  Proof.existence_bound k d₁ d₂ hk hd₁ hd h

/-- Non-existence half in the strong, constructive `Nonempty`-intersection
form. The underlying `Proof.strong_nonexistence` produces
the `¬ Disjoint` witness; `Set.not_disjoint_iff_nonempty_inter` exhibits the actual
collision point `kA ∩ B`. -/
theorem erdos_1112_strong_nonexistence (k d₁ d₂ : ℕ) (hk : 3 ≤ k)
    (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) (h : d₂ ≤ k) (R : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, IsVarLacunaryWith R b ∧
      ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a →
        (kFoldSumset k a ∩ Set.range b).Nonempty := by
  obtain ⟨b, hb, hdef⟩ := Proof.strong_nonexistence k d₁ d₂ hk hd₁ hd h R
  exact ⟨b, hb, fun a ha => Set.not_disjoint_iff_nonempty_inter.mp (hdef a ha)⟩

/-- **Erdős Problem 1112, the dichotomy**: `r` exists iff
`d₂ ≥ k + 1`. Derived from the two halves exactly as in paper Part IV. -/
theorem erdos_1112 (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) :
    Question k d₁ d₂ ↔ k + 1 ≤ d₂ := by
  constructor
  · rintro ⟨r, hr⟩
    by_contra hlt
    push_neg at hlt
    obtain ⟨b, hb, hdef⟩ :=
      erdos_1112_strong_nonexistence k d₁ d₂ hk hd₁ hd (by omega) (fun _ => r)
    obtain ⟨a, ha, hdisj⟩ := hr b (isVarLacunaryWith_const_iff.mp hb)
    exact (Set.not_disjoint_iff_nonempty_inter.mpr (hdef a ha)) hdisj
  · intro h
    exact ⟨192 * d₂, erdos_1112_existence_bound k d₁ d₂ hk hd₁ hd h⟩

end Erdos1112
