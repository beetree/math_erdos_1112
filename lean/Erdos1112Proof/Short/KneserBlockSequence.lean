/- The block-growth density/cofinite dichotomy, in fully generic form, for
the density route documented in `Short/KneserDensity/README.md`.

Given a fair, monotone/antitone sequence of pairs `(A_n, B_n)` with `0 ∈
B_n`, `B_n` infinite, constant joint density `d`, `A_n + B_n ⊆ C` for an
ambient set `C`, and `A_n` containing intervals of every length at some
stage, either `C` is cofinite or `d ≤ lowerDensity C`.

Proof: for each interval length `L`, `finite_absorption`
(`Short/DensityLimit.lean`) pushes the length-`L` interval forward to a
stage `j` where it is fully absorbed by `B_j`; shifting `A_j` down by the
interval's base point (`shiftedDown`, `Short/KneserShift.lean`) turns that
absorption into exactly the hypothesis of `lane_theorem13_absorbed`
(`Short/KneserBlocks.lean`) with `k := L`, discharging its `mann_count`
hypothesis with `KneserMann.mann_count`. Density invariance under
`shiftedDown` transports the conclusion back to `C`. Letting `L → ∞`
(`L/(L+1) → 1`) closes the analytic limit.

`lane_theorem13_absorbed`'s own conclusion is cofiniteness (`AsymEq _
Set.univ`), not just an AP tail; the transport here preserves that all the
way to `C`, giving the stronger dichotomy (`C` cofinite, not just
`HasAPTail C` — though the latter follows immediately, see
`HasAPTail_or_le_lowerDensity` at the end). -/
import Erdos1112Proof.Short.DensityLimit
import Erdos1112Proof.Short.KneserShift
import Erdos1112Proof.Short.KneserBlocks
import Erdos1112Proof.Short.KneserMann
import Erdos1112Proof.Short.DensityIteration

namespace Erdos1112.Proof.Short

open Erdos1112.Proof.Short.KneserDensity
open scoped Pointwise

/-! ### The shift-transport of cofiniteness -/

/-- If the shifted-down-and-summed set is cofinite (`AsymEq _ Set.univ`),
so is the original sum `A+B`. Strictly stronger than
`HasAPTail.of_shiftedDown_add` (`Short/KneserShift.lean`, which only
transports the weaker `HasAPTail`): here the transported set literally
covers a full tail of `ℕ`, not just an arithmetic progression within one. -/
theorem AsymEq_univ_of_shiftedDown_add {A B : Set ℕ} {x : ℕ}
    (h : AsymEq (shiftedDown A x + B) Set.univ) : AsymEq (A + B) Set.univ := by
  obtain ⟨N, hN⟩ := h
  refine ⟨x + N, fun z hz => ?_⟩
  simp only [Set.mem_univ, iff_true]
  have hy : (z - x) ≥ N := by omega
  have hmem : (z - x) ∈ shiftedDown A x + B := (hN (z - x) hy).mpr (Set.mem_univ _)
  have hz' : z = x + (z - x) := by omega
  rw [hz']
  exact shiftedUp_add_shiftedDown_subset A B x
    (Set.mem_image_of_mem (fun n => x + n) hmem)

/-! ### The per-length quantitative bound -/

/-- **Reusable quantitative bound, for each interval length `L`.** Given a
fair, monotone/antitone sequence of pairs with `0 ∈ B_n`, `B_n` infinite,
constant joint density `d`, `A_n+B_n ⊆ C`, and *some* stage `n` whose first
component contains a length-`L` interval starting at `x`, either `C` is
cofinite or `C`'s density is already at the `L`-th quantitative floor
`L/(L+1) · d`. This is exactly Lane's Theorem 13 bound (via
`lane_theorem13_absorbed`) transported from the shifted, absorbed pair back
to the ambient `C`. -/
theorem block_sequence_bound_L {A B : ℕ → Set ℕ} {C : Set ℕ} {d : ℝ}
    (hmono : Monotone A) (hanti : Antitone B) (hfair : FairAbsorption A B)
    (hB0 : ∀ n, 0 ∈ B n) (hBinf : ∀ n, (B n).Infinite)
    (hsum : ∀ n, A n + B n ⊆ C) (hd : ∀ n, twoFoldLowerDensity (A n) (B n) = d)
    {L n x : ℕ} (hLpos : 0 < L) (hint : ∀ i < L, x + i ∈ A n) :
    AsymEq C Set.univ ∨ (L : ℝ) / (L + 1) * d ≤ lowerDensity C := by
  classical
  have hxA : ∀ e ∈ Finset.Icc x (x + L - 1), e ∈ A n := by
    intro e he
    simp only [Finset.mem_Icc] at he
    have : e = x + (e - x) := by omega
    rw [this]
    exact hint (e - x) (by omega)
  obtain ⟨j, hjn, habsE⟩ := finite_absorption hfair hmono hanti n (Finset.Icc x (x + L - 1)) hxA
  have habs : ∀ i < L, ∀ b ∈ B j, i + b ∈ shiftedDown (A j) x := by
    intro i hi b hb
    show x + (i + b) ∈ A j
    have hmem : x + i ∈ Finset.Icc x (x + L - 1) := by
      simp only [Finset.mem_Icc]; omega
    have := habsE (x + i) hmem b hb
    have heq : x + (i + b) = x + i + b := by ring
    rwa [heq]
  have hx0A : x ∈ A n := hint 0 hLpos
  have hxAj : x ∈ A j := hmono hjn hx0A
  have h0shift : (0 : ℕ) ∈ shiftedDown (A j) x := by simpa using hxAj
  have hB0j : (0 : ℕ) ∈ B j := hB0 j
  have hBjInf : (B j).Infinite := hBinf j
  have hlane := lane_theorem13_absorbed h0shift hB0j hLpos hBjInf habs @KneserMann.mann_count
  have hdensEq : twoFoldLowerDensity (shiftedDown (A j) x) (B j) = d := by
    rw [twoFoldLowerDensity_shiftedDown_left]; exact hd j
  rw [hdensEq] at hlane
  rcases hlane with hAP | hden
  · left
    have h1 := AsymEq_univ_of_shiftedDown_add hAP
    obtain ⟨N, hN⟩ := h1
    refine ⟨N, fun y hy => ?_⟩
    simp only [Set.mem_univ, iff_true]
    have hyAB : y ∈ A j + B j := (hN y hy).mpr (Set.mem_univ _)
    exact hsum j hyAB
  · right
    have hsub : shiftedDown (A j) x + B j ⊆ shiftedDown (A j + B j) x := by
      rintro _ ⟨a, ha, b, hb, rfl⟩
      refine ⟨x + a, ha, b, hb, ?_⟩
      ring
    have hmono1 : lowerDensity (shiftedDown (A j) x + B j) ≤
        lowerDensity (shiftedDown (A j + B j) x) := lowerDensity_mono hsub
    have heq2 : lowerDensity (shiftedDown (A j + B j) x) = lowerDensity (A j + B j) :=
      lowerDensity_shiftedDown (A j + B j) x
    have hmono2 : lowerDensity (A j + B j) ≤ lowerDensity C := lowerDensity_mono (hsum j)
    linarith [hden, hmono1, heq2, hmono2]

/-! ### The main dichotomy: `L → ∞` -/

/-- **Main theorem.** Either `C` is cofinite, or `C`'s lower density is at
least the constant joint density `d` of the fair sequence. This is the
*stronger* dichotomy the compression wrapper may need — full cofiniteness
of `C`, not just `HasAPTail C` — obtained by the same proof at every `L`. -/
theorem block_sequence_dichotomy {A B : ℕ → Set ℕ} {C : Set ℕ} {d : ℝ}
    (hmono : Monotone A) (hanti : Antitone B) (hfair : FairAbsorption A B)
    (hB0 : ∀ n, 0 ∈ B n) (hBinf : ∀ n, (B n).Infinite)
    (hsum : ∀ n, A n + B n ⊆ C) (hd : ∀ n, twoFoldLowerDensity (A n) (B n) = d)
    (hlong : ∀ L : ℕ, ∃ n x, ∀ i < L, x + i ∈ A n) :
    AsymEq C Set.univ ∨ d ≤ lowerDensity C := by
  by_cases hAP : AsymEq C Set.univ
  · exact Or.inl hAP
  · right
    have hall : ∀ L : ℕ, 0 < L → (L : ℝ) / (L + 1) * d ≤ lowerDensity C := by
      intro L hLpos
      obtain ⟨n, x, hint⟩ := hlong L
      rcases block_sequence_bound_L hmono hanti hfair hB0 hBinf hsum hd hLpos hint with h | h
      · exact absurd h hAP
      · exact h
    have htend : Filter.Tendsto (fun L : ℕ => (L : ℝ) / (L + 1) * d) Filter.atTop (nhds d) := by
      have h1 := (tendsto_natCast_div_add_atTop (1 : ℝ)).mul_const d
      simpa using h1
    refine le_of_tendsto' htend (fun L => ?_)
    rcases Nat.eq_zero_or_pos L with hL0 | hLpos
    · subst hL0
      simp only [Nat.cast_zero, zero_div, zero_mul]
      exact lowerDensity_nonneg C
    · exact hall L hLpos

/-! ### `HasAPTail` corollary, for callers matching `DensityIteration`'s
shape -/

/-- The weaker `HasAPTail`-flavored dichotomy, immediate from
`block_sequence_dichotomy` since a cofinite set trivially has an AP tail
(`q := 1`). Provided for convenience for a caller expecting `hkn`'s exact
output shape; the primary result above is strictly stronger. -/
theorem block_sequence_hasAPTail_dichotomy {A B : ℕ → Set ℕ} {C : Set ℕ} {d : ℝ}
    (hmono : Monotone A) (hanti : Antitone B) (hfair : FairAbsorption A B)
    (hB0 : ∀ n, 0 ∈ B n) (hBinf : ∀ n, (B n).Infinite)
    (hsum : ∀ n, A n + B n ⊆ C) (hd : ∀ n, twoFoldLowerDensity (A n) (B n) = d)
    (hlong : ∀ L : ℕ, ∃ n x, ∀ i < L, x + i ∈ A n) :
    HasAPTail C ∨ d ≤ lowerDensity C := by
  rcases block_sequence_dichotomy hmono hanti hfair hB0 hBinf hsum hd hlong with hAP | hden
  · obtain ⟨N, hN⟩ := hAP
    exact Or.inl ⟨1, one_pos, N, fun j => (hN (N + 1 * j) (by omega)).mpr (Set.mem_univ _)⟩
  · exact Or.inr hden

end Erdos1112.Proof.Short
