/-
Statement forms for the paper’s finite interval lemma (SHARP).
-/
import Erdos1112Proof.SubsetSums

namespace Erdos1112
namespace Proof

/-- (SHARP) for the triple alphabet `{a, b, M}`: some multiset of at most
`M − 1` elements drawn from `{a,b,M}` has subset sums containing `M`
consecutive integers. -/
def SharpTriple (a b M : ℕ) : Prop :=
  ∃ S : Multiset ℕ, (∀ x ∈ S, x = a ∨ x = b ∨ x = M) ∧
    S.card ≤ M - 1 ∧ HasRun (subsetSums S) M

/-- (SHARP) at maximum `M`, for all alphabets: every finite `G` of at least
three positive integers with `gcd G = 1` and maximum `M` admits a multiset of
at most `M−1` of its elements whose subset sums contain `M` consecutive
integers. (`max` is encoded as `M ∈ G ∧ ∀ g ∈ G, g ≤ M`.) -/
def SharpAt (M : ℕ) : Prop :=
  ∀ G : Finset ℕ, (∀ g ∈ G, 0 < g) → 3 ≤ G.card → G.gcd id = 1 →
    (∀ g ∈ G, g ≤ M) → M ∈ G →
    ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ G) ∧ S.card ≤ M - 1 ∧
      HasRun (subsetSums S) M


end Proof
end Erdos1112
