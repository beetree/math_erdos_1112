/- Elementary steps surrounding the short paper's Kneser shortcut:
linear growth gives a density-count bound, and eventual periodicity gives a
congruence-class tail. The density structure theorem is a separate dependency;
see PROGRESS.md for its verification status. -/
import Mathlib
import Erdos1112Proof.Short.TailCovering

namespace Erdos1112.Proof.Short

open Filter
open scoped Pointwise

/-! ### Periodicity ⟹ tail-covering

The elementary half of the Kneser dichotomy: an eventually-periodic `k`-fold
sumset that is nonempty in its periodic range already contains a whole
congruence-class tail. -/

/-- If `kFoldSumset k a` is closed under `+ m` from `X₀` on, and it contains
some element `x₁ ≥ X₀`, then it contains the whole congruence-class tail of
`x₁` mod `m`. Only the forward-closure direction of periodicity is needed. -/
theorem tailCovering_of_eventually_periodic {k : ℕ} {a : ℕ → ℕ} {m X₀ x₁ : ℕ}
    (hm : 0 < m)
    (hper : ∀ x, X₀ ≤ x → x ∈ kFoldSumset k a → x + m ∈ kFoldSumset k a)
    (hX₀ : X₀ ≤ x₁) (hx₁ : x₁ ∈ kFoldSumset k a) :
    Erdos1112.Proof.TailCovering k a := by
  have hstep : ∀ j, x₁ + m * j ∈ kFoldSumset k a := by
    intro j
    induction j with
    | zero => simpa using hx₁
    | succ j ih =>
      have hxj : X₀ ≤ x₁ + m * j := by omega
      have hnext := hper (x₁ + m * j) hxj ih
      have he : x₁ + m * j + m = x₁ + m * (j + 1) := by ring
      rwa [he] at hnext
  refine ⟨m, hm, x₁ % m, Nat.mod_lt _ hm, x₁, fun x hx hxmod => ?_⟩
  have hdvd : m ∣ x - x₁ := (Nat.modEq_iff_dvd' hx).mp hxmod.symm
  obtain ⟨j, hj⟩ := hdvd
  have hxeq : x = x₁ + m * j := by omega
  rw [hxeq]
  exact hstep j

/-! ### Growth bound ⟹ density-count bound

The paper's opening reduction: `p_n ≤ c*n+C` eventually forces, for every
large `N`, an index `n ≈ N/c` with `p_n ≤ N` — the (lower) density of `P` is
at least `1/c`. -/

/-- **Growth ⟹ density-count bound.** If `p_n ≤ c*n + C` eventually with
`0 < c`, then for every sufficiently large `N` there is an index `n` with
`p n ≤ N` and `n` at least `N/c - (C/c + 1)`. This is the paper's "for large
`N` take `n = ⌊(N-C)/c⌋`; then `p_n ≤ N`" step, quantified. -/
theorem exists_index_le_of_growth {p : ℕ → ℕ} {c C : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ n in atTop, (p n : ℝ) ≤ c * n + C) :
    ∀ᶠ N : ℕ in atTop, ∃ n : ℕ, p n ≤ N ∧ (N : ℝ) / c - (C / c + 1) ≤ n := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hbound
  refine eventually_atTop.mpr ⟨⌈c * n₀ + C⌉₊, fun N hN => ?_⟩
  have hNr : (c * n₀ + C : ℝ) ≤ N := (Nat.le_ceil (c * n₀ + C)).trans (by exact_mod_cast hN)
  have hNC0 : (0 : ℝ) ≤ ((N : ℝ) - C) / c := by
    have h2 : (0 : ℝ) ≤ (N : ℝ) - C := by nlinarith [mul_nonneg (Nat.cast_nonneg n₀) hc.le]
    positivity
  have hn0 : n₀ ≤ ⌊((N : ℝ) - C) / c⌋₊ := by
    apply Nat.le_floor
    rw [le_div_iff₀ hc]
    nlinarith
  have hbn : (p ⌊((N : ℝ) - C) / c⌋₊ : ℝ) ≤ c * ⌊((N : ℝ) - C) / c⌋₊ + C := hn₀ _ hn0
  have hnle : (⌊((N : ℝ) - C) / c⌋₊ : ℝ) ≤ ((N : ℝ) - C) / c := Nat.floor_le hNC0
  have hpnN : (p ⌊((N : ℝ) - C) / c⌋₊ : ℝ) ≤ N := by
    have hcn : c * (⌊((N : ℝ) - C) / c⌋₊ : ℝ) ≤ c * (((N : ℝ) - C) / c) :=
      mul_le_mul_of_nonneg_left hnle hc.le
    rw [mul_div_cancel₀ _ hc.ne'] at hcn
    linarith
  have hpnN' : p ⌊((N : ℝ) - C) / c⌋₊ ≤ N := by exact_mod_cast hpnN
  have hnlb : ((N : ℝ) - C) / c < (⌊((N : ℝ) - C) / c⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsub : ((N : ℝ) - C) / c = (N : ℝ) / c - C / c := sub_div _ _ _
  refine ⟨⌊((N : ℝ) - C) / c⌋₊, hpnN', ?_⟩
  linarith [hsub, hnlb]

open scoped Classical

/-- Counting the first `n+1` distinct sequence values below `N`. -/
lemma prefix_count_le {p : ℕ → ℕ} (hmono : StrictMono p) {n N : ℕ}
    (hpn : p n ≤ N) :
    n + 1 ≤ ((Finset.range (N + 1)).filter (fun x => x ∈ Set.range p)).card := by
  have hsub : (Finset.range (n + 1)).image p ⊆
      (Finset.range (N + 1)).filter (fun x => x ∈ Set.range p) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hin : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    have hiN := (hmono.monotone hin).trans hpn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨i, rfl⟩⟩
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hmono.injective, Finset.card_range] using hc

/-- The linear-growth hypothesis supplies the quantitative count estimate
underlying the lower-asymptotic-density bound `d̲(range p) ≥ 1/c`. -/
theorem count_bound_of_growth {p : ℕ → ℕ} {c C : ℝ}
    (hmono : StrictMono p) (hc : 0 < c)
    (hbound : ∀ᶠ n in atTop, (p n : ℝ) ≤ c * n + C) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) / c - C / c ≤
      (((Finset.range (N + 1)).filter (fun x => x ∈ Set.range p)).card : ℝ) := by
  filter_upwards [exists_index_le_of_growth hc hbound] with N hN
  obtain ⟨n, hpn, hn⟩ := hN
  have hh := prefix_count_le hmono hpn
  have hr : (n : ℝ) + 1 ≤
      (((Finset.range (N + 1)).filter (fun x => x ∈ Set.range p)).card : ℝ) := by
    exact_mod_cast hh
  linarith

end Erdos1112.Proof.Short
