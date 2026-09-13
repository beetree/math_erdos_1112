/- The paper's density shortcut, walk covering theorem and universal diagonal
construction, with the Kneser and SHARP dependencies fully discharged. -/
import Erdos1112Proof.Short.Assembly
import Erdos1112Proof.Short.Certificate
import Erdos1112Proof.Short.KneserWeak

namespace Erdos1112.Proof.Short

/-- Growth below the summand count forces a congruence-class tail. -/
theorem density_shortcut {k : ℕ} {P : ℕ → ℕ} {c C : ℝ}
    (hP0 : P 0=0) (hmono : StrictMono P) (hc : 0 < c) (hck : c < (k:ℝ))
    (hbound : ∀ᶠ n in Filter.atTop, (P n:ℝ) ≤ c*n+C) : TailCovering k P :=
  tailCovering_of_growth_lt KneserWeak.weak_kneser hP0 hmono hc hck hbound

/-- Every admissible walk with gaps at most `k` is `k`-tail-covering. -/
theorem all_tailCovering {k d₁ d₂ : ℕ} (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (hd₂ : d₂ ≤ k) {a : ℕ → ℕ} (hgaps : HasGapsIn d₁ d₂ a) : TailCovering k a :=
  tailCovering_of_normalized_cases (normalized_cases hk KneserWeak.weak_kneser) hd₁ hgaps hd₂

/-- One sequence with arbitrary prescribed successive ratios meets the sumset
of every admissible walk below the threshold. -/
theorem strong_nonexistence (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (hd₂ : d₂ ≤ k) (R : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, IsVarLacunaryWith R b ∧
      ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a →
        ¬ Disjoint (kFoldSumset k a) (Set.range b) :=
  strong_nonexistence_of_tailCovering k d₁ d₂ R
    (fun _a ha => all_tailCovering hk hd₁ hd₂ ha)

end Erdos1112.Proof.Short
