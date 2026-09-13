/- Follow-up to `Short/Binary.lean`: the bridge between the two zero-frequency
alternatives (`ZeroFreqLiminfZero` vs. its failure) and the normalized
two-letter case (`Short/Normalization.normalized_walk`).

1. `growth_bound_of_not_liminfZero`: failure of `ZeroFreqLiminfZero` forces a
   positive linear lower bound on the zero-count, hence `a n ≤ c*n + C`
   eventually with `0 < c < k` — the paper's "if `liminf z_n/n > 0`, choose
   `0 < γ ≤ 1` … then `p_n ≤ (k − eγ)n`" step, exact arithmetic throughout,
   feeding the density branch (owned elsewhere) without assuming Kneser.
2. `binary_tail_covering_normalized`: `binary_tail_covering` needs
   `HasGapsIn`, which needs a positive initial point, but `normalized_walk`
   produces `P 0 = 0`. Bridges this via the shift `P ∘ succ` (whose initial
   point is positive by `StrictMono`) plus a direct `TailCovering` transport
   back along that shift (elementary: `kFoldSumset` membership only shifts
   witness indices by one, no rescaling machinery needed).
3. `binary_dichotomy`: packages both as an unconditional disjunction — no
   unresolved Kneser hypothesis on either side. Both branches share the same
   `P ∘ succ` shift and the same binary encoding `gapCode`, so the dichotomy
   is a genuine case split on one proposition (`ZeroFreqLiminfZero (gapCode
   P k)`), not two mismatched encodings. -/
import Erdos1112Proof.Short.Binary

namespace Erdos1112.Proof.Short

/-! ### 1. Growth bound from failure of `ZeroFreqLiminfZero` -/

/-- Unfolding the negation: failure of `ZeroFreqLiminfZero` produces an
explicit rate `L` and threshold `N` past which the zero-count is bounded
*below* linearly, `n ≤ z_n · L`. -/
theorem zero_count_lowerBound_of_not_liminfZero {h : ℕ → Bool}
    (hnlim : ¬ ZeroFreqLiminfZero h) :
    ∃ L N : ℕ, 0 < L ∧ ∀ n, N ≤ n → n ≤ (n - qCount h n) * L := by
  unfold ZeroFreqLiminfZero at hnlim
  push_neg at hnlim
  obtain ⟨L, hLpos, N, hN⟩ := hnlim
  exact ⟨L, N, hLpos, hN⟩

/-- The affine identity `a n = a 0 + δ·n + e·qCount h n` forced by the
`{δ,k}` encoding. No `HasGapsIn` is assumed: `hδ : 0 < δ` alone forces
`gap a n = a (n+1) - a n` (natural subtraction) to be a genuine positive
difference, so the recursion is exact. -/
theorem affine_eq_of_hgap {a : ℕ → ℕ} {h : ℕ → Bool} {δ e : ℕ} (hδ : 0 < δ)
    (hgap : ∀ n, gap a n = δ + e * (if h (n + 1) then 1 else 0)) :
    ∀ n, a n = a 0 + δ * n + e * qCount h n := by
  intro n
  induction n with
  | zero => simp [qCount]
  | succ n ih =>
      have hg := hgap n
      unfold gap at hg
      rw [qCount_succ]
      have e1 : δ * (n + 1) = δ * n + δ := by ring
      cases hc : h (n + 1) with
      | false => simp [hc] at hg ⊢; omega
      | true =>
          simp [hc] at hg ⊢
          have e2 : e * (qCount h n + 1) = e * qCount h n + e := by ring
          omega

/-- Pure `ℕ` core of the growth bound (no division): multiplying through by
the rate `L` from `zero_count_lowerBound_of_not_liminfZero` turns the affine
identity plus the zero-count lower bound into an explicit linear inequality
with no fractional arithmetic. -/
theorem nat_growth_bound {a : ℕ → ℕ} {h : ℕ → Bool} {δ e k L N : ℕ}
    (hδ : 0 < δ) (hk_eq : δ + e = k)
    (hgap : ∀ n, gap a n = δ + e * (if h (n + 1) then 1 else 0))
    (hzn : ∀ n, N ≤ n → n ≤ (n - qCount h n) * L) :
    ∀ n, N ≤ n → a n * L + e * n ≤ k * L * n + a 0 * L := by
  intro n hn
  have haffn := affine_eq_of_hgap hδ hgap n
  have hqle : qCount h n ≤ n := qCount_le h n
  have hzn' := hzn n hn
  have hexp : (n - qCount h n) * L = n * L - qCount h n * L := by
    rw [Nat.sub_mul]
  rw [hexp] at hzn'
  have hqL : qCount h n * L ≤ n * L := Nat.mul_le_mul_right L hqle
  have hkey : n + qCount h n * L ≤ n * L := by omega
  have he' : e * (n + qCount h n * L) ≤ e * (n * L) := Nat.mul_le_mul_left e hkey
  have hdist : e * (n + qCount h n * L) = e * n + e * (qCount h n * L) := by ring
  rw [hdist] at he'
  have hstep : a n * L = a 0 * L + δ * n * L + e * (qCount h n * L) := by
    rw [haffn]; ring
  have hkLn : k * L * n = (δ + e) * L * n := by rw [hk_eq]
  have hkLn2 : (δ + e) * L * n = δ * n * L + e * (n * L) := by ring
  rw [hstep, hkLn, hkLn2]
  omega

/-- **Density-free growth bound.** If `ZeroFreqLiminfZero h` fails, the
`{δ,k}`-encoded walk `a` satisfies `a n ≤ c·n + C` eventually, for *real*
constants `0 < c < k` — the paper's complementary branch to the density
shortcut, ready to feed a Kneser-based density theorem (owned elsewhere)
without that theorem being assumed here. -/
theorem growth_bound_of_not_liminfZero {a : ℕ → ℕ} {h : ℕ → Bool} {δ e k : ℕ}
    (hδ : 0 < δ) (he : 0 < e) (hk_eq : δ + e = k)
    (hgap : ∀ n, gap a n = δ + e * (if h (n + 1) then 1 else 0))
    (hnlim : ¬ ZeroFreqLiminfZero h) :
    ∃ c C : ℝ, 0 < c ∧ c < (k : ℝ) ∧
      ∀ᶠ n in Filter.atTop, (a n : ℝ) ≤ c * n + C := by
  obtain ⟨L, N, hLpos, hN⟩ := zero_count_lowerBound_of_not_liminfZero hnlim
  have hnat := nat_growth_bound (a := a) (h := h) hδ hk_eq hgap hN
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hek : e < k := by omega
  have hkR : (e : ℝ) < k := by exact_mod_cast hek
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLpos
  refine ⟨(k : ℝ) - (e : ℝ) / L, (a 0 : ℝ), ?_, ?_,
    Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  · have h1 : (e : ℝ) / L ≤ e := by rw [div_le_iff₀ hLR]; nlinarith [hL1, heR]
    linarith
  · have h2 : (0 : ℝ) < (e : ℝ) / L := div_pos heR hLR
    linarith
  · have hn' := hnat n hn
    have hcast : (a n : ℝ) * L + (e : ℝ) * n ≤ (k : ℝ) * L * n + (a 0 : ℝ) * L := by
      exact_mod_cast hn'
    have heq : ((k : ℝ) - (e : ℝ) / L) * n + (a 0 : ℝ) =
        ((k : ℝ) * L * n - (e : ℝ) * n + (a 0 : ℝ) * L) / L := by
      field_simp
    rw [heq, le_div_iff₀ hLR]
    nlinarith [hcast]

/-! ### 2. Bridging `normalized_walk`'s `P 0 = 0` to `binary_tail_covering` -/

/-- The binary encoding of a `{δ,k}`-gapped walk directly from its own
gaps: `true` at `m` means `gap P m = k`. -/
def gapCode (P : ℕ → ℕ) (k : ℕ) : ℕ → Bool := fun m => decide (gap P m = k)

/-- `TailCovering` transports backwards along an index shift by one: the
`k`-fold sumset of the shift is contained in the original `k`-fold sumset
(shift every witness index by one), so covering the shift's tail already
covers the original's tail. No rescaling is needed since the shift changes
no *values*, only which indices of `a` are visible. -/
theorem tailCovering_of_shift_succ {k : ℕ} {a : ℕ → ℕ}
    (hcov : TailCovering k (fun n => a (n + 1))) : TailCovering k a := by
  obtain ⟨m, hm, ρ, hρ, X₀, hX⟩ := hcov
  exact ⟨m, hm, ρ, hρ, X₀, fun x hx hxmod =>
    let ⟨f, hf⟩ := hX x hx hxmod
    ⟨fun j => f j + 1, hf⟩⟩

/-- Shared setup for both branches of the dichotomy: the shift `P ∘ succ`
has positive initial point (by `StrictMono`, since `P 0 = 0`), gaps still
exactly encoded by `gapCode P k` (the *same* encoding, evaluated one step
later, matching the shift), and consequently `HasGapsIn δ k` on the shift. -/
theorem shift_setup {k δ : ℕ} {P : ℕ → ℕ} (hP0 : P 0 = 0) (hPmono : StrictMono P)
    (hδ : 0 < δ) (hδk : δ < k)
    (hgap : ∀ n, gap P n = δ ∨ gap P n = k) :
    HasGapsIn δ k (fun m => P (m + 1)) ∧
      (∀ n, gap (fun m => P (m + 1)) n =
        δ + (k - δ) * (if gapCode P k (n + 1) then 1 else 0)) := by
  have ha'0 : 0 < P 1 := by
    have h01 := hPmono (show (0 : ℕ) < 1 by norm_num)
    omega
  have hgap' : ∀ n, gap (fun m => P (m + 1)) n =
      δ + (k - δ) * (if gapCode P k (n + 1) then 1 else 0) := by
    intro n
    have hga : gap (fun m => P (m + 1)) n = gap P (n + 1) := by
      show P (n + 1 + 1) - P (n + 1) = P (n + 1 + 1) - P (n + 1)
      rfl
    rw [hga]
    rcases hgap (n + 1) with hδcase | hkcase
    · have hne : gap P (n + 1) ≠ k := by omega
      have hcf : gapCode P k (n + 1) = false := decide_eq_false hne
      rw [hcf]; simpa using hδcase
    · have hct : gapCode P k (n + 1) = true := decide_eq_true hkcase
      rw [hct]; simp; omega
  have hbound' : ∀ i, δ ≤ gap (fun m => P (m + 1)) i ∧ gap (fun m => P (m + 1)) i ≤ k := by
    intro i
    have hgi := hgap' i
    cases hc : gapCode P k (i + 1) with
    | false => rw [hc] at hgi; simp at hgi; omega
    | true => rw [hc] at hgi; simp at hgi; omega
  have hgaps' : HasGapsIn δ k (fun m => P (m + 1)) := by
    refine ⟨ha'0, fun i => ?_⟩
    have hb := hbound' i
    unfold gap at hb
    omega
  exact ⟨hgaps', hgap'⟩

/-- **Normalized zero-liminf binary tail-covering.** For `P` with `P 0 = 0`
and `StrictMono P`, all gaps in `{δ, k}` (`gcd(δ,k) = 1`), `δ` recurring,
and vanishing liminf zero-frequency (of the walk's own `k`-gap indicator),
`P` is `k`-tail-covering. Bridges `binary_tail_covering`'s `HasGapsIn`
(which needs `0 < a 0`) via the shift `a' := P ∘ succ` (positive at `0` by
`StrictMono`), then transports the conclusion back with
`tailCovering_of_shift_succ`. -/
theorem binary_tail_covering_normalized {k δ : ℕ} {P : ℕ → ℕ} (hk : 3 ≤ k)
    (hP0 : P 0 = 0) (hPmono : StrictMono P)
    (hδ : 0 < δ) (hδk : δ < k) (hco : Nat.Coprime δ k)
    (hgap : ∀ n, gap P n = δ ∨ gap P n = k)
    (hrecur : ∀ N, ∃ n, N ≤ n ∧ gap P n = δ)
    (hlim : ZeroFreqLiminfZero (gapCode P k)) :
    TailCovering k P := by
  have he : 0 < k - δ := by omega
  have hk_eq : δ + (k - δ) = k := by omega
  obtain ⟨hgaps', hgap'⟩ := shift_setup hP0 hPmono hδ hδk hgap
  have hzr : ZeroRecurs (gapCode P k) := by
    intro N
    obtain ⟨m, hmN, hm⟩ := hrecur (N + 1)
    refine ⟨m - 1, by omega, ?_⟩
    have he1 : m - 1 + 1 = m := by omega
    show gapCode P k (m - 1 + 1) = false
    rw [he1, gapCode, hm]
    exact decide_eq_false (by omega)
  have hcov' : TailCovering k (fun m => P (m + 1)) :=
    binary_tail_covering hk hgaps' (gapCode P k) δ (k - δ) hδ he hco hk_eq hgap' hzr hlim
  exact tailCovering_of_shift_succ hcov'

/-! ### 3. The unconditional dichotomy -/

/-- **Unconditional dichotomy, no Kneser hypothesis.** Either the growth
bound `p_n ≤ c·n + C` (`0 < c < k`) holds — feeding the density branch — or
`P` is already `k`-tail-covering by the binary argument. Exactly one of the
two paper branches always applies; neither is assumed, and both branches
share the same shift and the same binary encoding (`gapCode P k`), so this
is a genuine case split on a single proposition. -/
theorem binary_dichotomy {k δ : ℕ} {P : ℕ → ℕ} (hk : 3 ≤ k)
    (hP0 : P 0 = 0) (hPmono : StrictMono P)
    (hδ : 0 < δ) (hδk : δ < k) (hco : Nat.Coprime δ k)
    (hgap : ∀ n, gap P n = δ ∨ gap P n = k)
    (hrecur : ∀ N, ∃ n, N ≤ n ∧ gap P n = δ) :
    (∃ c C : ℝ, 0 < c ∧ c < (k : ℝ) ∧
        ∀ᶠ n in Filter.atTop, (P n : ℝ) ≤ c * n + C) ∨
      TailCovering k P := by
  by_cases hlim : ZeroFreqLiminfZero (gapCode P k)
  · exact Or.inr (binary_tail_covering_normalized hk hP0 hPmono hδ hδk hco hgap hrecur hlim)
  · refine Or.inl ?_
    have he : 0 < k - δ := by omega
    have hk_eq : δ + (k - δ) = k := by omega
    obtain ⟨-, hgap'⟩ := shift_setup hP0 hPmono hδ hδk hgap
    obtain ⟨c, C, hc0, hck, hbnd⟩ :=
      growth_bound_of_not_liminfZero (a := fun m => P (m + 1)) (h := gapCode P k)
        hδ he hk_eq hgap' hlim
    refine ⟨c, C - c, hc0, hck, ?_⟩
    rw [Filter.eventually_atTop] at hbnd ⊢
    obtain ⟨N, hN⟩ := hbnd
    refine ⟨N + 1, fun m hm => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have := hN n (by omega)
    push_cast
    push_cast at this
    linarith

end Erdos1112.Proof.Short
