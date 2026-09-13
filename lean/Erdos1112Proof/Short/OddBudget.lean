/- Short paper `lem:eta`, odd `a = 2n+1` case: the arithmetic budget
inequalities `K + ⌈(M-1+S)/a⌉ ≤ M-1` (paper `eq:path-cost`/`eq:crude-budget`
specialized to the odd-`a` sub-cases), with the ceiling written as
`(T+a-1)/a`. This file only proves the arithmetic; it takes the paper's
designated representative heights `K`, `S` as given hypotheses and does not
reprove residue coverage (that is `ResidueFrame`/`ResiduePath`) or the
explicit `η=2, λ=0, h∈{1,2}` constructions (that is `Short/OddSpacing.lean`).
No SHARP table/lift/staircase machinery. -/
import Erdos1112Proof.Short.Intervals

namespace Erdos1112.Proof.Short

/-- Additive (subtraction-free) form of the paper's `M-1-K` slack bound. -/
theorem budget_sub_of_add {a K M S : ℕ} (hK : K ≤ M - 1)
    (h : M - 1 + S + a * K ≤ a * (M - 1)) : M - 1 + S ≤ a * (M - 1 - K) := by
  have heq : a * (M - 1) = a * (M - 1 - K) + a * K := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hK]
  omega

/-- The paper's slack bound `M-1+S ≤ a*(M-1-K)` upgrades to the ceiling
budget `K + ⌈(M-1+S)/a⌉ ≤ M-1`, with the ceiling written as `(T+a-1)/a`. -/
theorem ceil_budget_of_le {a K M S : ℕ} (ha : 0 < a) (hK : K ≤ M - 1)
    (hS : M - 1 + S ≤ a * (M - 1 - K)) :
    K + (M - 1 + S + a - 1) / a ≤ M - 1 := by
  have hdiv : (M - 1 + S + a - 1) / a ≤ M - 1 - K := by
    rw [Nat.div_le_iff_le_mul_add_pred ha]
    omega
  omega

/-- Combined bridge: an additive slack bound directly gives the ceiling
budget `K + ⌈(M-1+S)/a⌉ ≤ M-1`. -/
theorem ceil_budget_of_add {a K M S : ℕ} (ha : 0 < a) (hK : K ≤ M - 1)
    (h : M - 1 + S + a * K ≤ a * (M - 1)) :
    K + (M - 1 + S + a - 1) / a ≤ M - 1 :=
  ceil_budget_of_le ha hK (budget_sub_of_add hK h)

/-- Odd `a = 2n+1`, generic case `K ≤ n` with `S ≤ K*M` (paper
`eq:crude-budget` at the worst `K = n`, slack `n(μ-2) ≥ 0`). -/
theorem odd_budget_generic {n a e h b M K S : ℕ} (hn : 2 ≤ n) (ha : a = 2 * n + 1)
    (hb : b = a + e) (hM : M = b + h) (he : 1 ≤ e) (hh1 : 1 ≤ h) (hK : K ≤ n)
    (hS : S ≤ K * M) :
    K + (M - 1 + S + a - 1) / a ≤ M - 1 := by
  have hKM : K ≤ M - 1 := by omega
  refine ceil_budget_of_add (by omega) hKM ?_
  have hworst : M - 1 + S + a * K ≤ M - 1 + K * M + a * K := by omega
  refine hworst.trans ?_
  obtain ⟨d, hd⟩ := Nat.le.dest hK
  obtain ⟨e', he'⟩ := Nat.exists_eq_add_of_le he
  obtain ⟨h', hh''⟩ := Nat.exists_eq_add_of_le hh1
  subst ha hb hM he' hh'' hd
  have hsub : (2 * (K + d) + 1 + (1 + e') + (1 + h') - 1 : ℕ) =
      2 * K + 2 * d + e' + h' + 2 := by omega
  rw [hsub]
  nlinarith [mul_nonneg (Nat.zero_le (K + d)) (Nat.zero_le (e' + h')),
    mul_nonneg (Nat.zero_le d) (Nat.zero_le (4 * K + 4 * d + e' + h' + 4))]

/-- Odd `a = 2n+1`, `η = 2`: `K = n+1`, `S = n*M`, `e = h + λ*a`. Excludes
the `λ = 0, h ∈ {1,2}` exceptional constructions, handled in
`Short/OddSpacing.lean`. -/
theorem odd_budget_eta_two {n h lam K S a b e M : ℕ}
    (hn : 2 ≤ n) (ha : a = 2 * n + 1) (hb : b = a + e) (hM : M = b + h)
    (hh1 : 1 ≤ h) (hcase : 1 ≤ lam ∨ 3 ≤ h) (he : e = h + lam * a)
    (hK : K = n + 1) (hS : S = n * M) :
    K + (M - 1 + S + a - 1) / a ≤ M - 1 := by
  subst_vars
  refine ceil_budget_of_add (by omega) (by omega) ?_
  have hsub : (2 * n + 1 + (h + lam * (2 * n + 1)) + h - 1 : ℕ) =
      2 * n + 2 * h + lam * (2 * n + 1) := by omega
  rw [hsub]
  rcases hcase with hl | hh3
  · nlinarith [Nat.mul_le_mul_left (n * (2 * n + 1)) hl,
      Nat.mul_le_mul_left (2 * n) hh1, sq_nonneg n]
  · nlinarith [Nat.mul_le_mul_left (2 * n) hh3, sq_nonneg n]

/-- Odd `a = 2n+1`, `η = -2`, `n ≥ 3`: the centered span `S = (n-1)*M`,
`K = n+1` (representatives `M^{n-1}, b^2`). -/
theorem odd_budget_eta_neg2_ge3 {n a e h b M K S : ℕ}
    (hn : 3 ≤ n) (ha : a = 2 * n + 1) (hb : b = a + e) (hM : M = b + h)
    (he : 1 ≤ e) (hh1 : 1 ≤ h) (hK : K = n + 1) (hS : S = (n - 1) * M) :
    K + (M - 1 + S + a - 1) / a ≤ M - 1 := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hKM : K ≤ M - 1 := by omega
  refine ceil_budget_of_add (by omega) hKM ?_
  subst_vars
  have hsub1 : (n' + 1 - 1 : ℕ) = n' := by omega
  rw [hsub1]
  have hsub2 : (2 * (n' + 1) + 1 + e + h - 1 : ℕ) = 2 * n' + e + h + 2 := by omega
  rw [hsub2]
  nlinarith [Nat.mul_le_mul_right (n' + 2) (show 2 ≤ e + h by omega)]

/-- Odd `a = 2n+1`, `η = -2`, `n = 2` (`a = 5`): the explicit representatives
`M, b, M+b, 2b, M+2b` give span `S = M+b`, `K = 3`. The congruence
`h ≡ 2e (mod 5)` together with pairwise coprimality excludes `e ∈ {1,2}`
(that exclusion is `ResidueFrame`/`ResiduePath`'s job); here we only need
the resulting bound `3 ≤ e`. -/
theorem odd_budget_eta_neg2_eq2 {e h b M K S : ℕ}
    (hb : b = 5 + e) (hM : M = b + h) (he3 : 3 ≤ e) (hh1 : 1 ≤ h)
    (hK : K = 3) (hS : S = M + b) :
    K + (M - 1 + S + 5 - 1) / 5 ≤ M - 1 := by
  have hKM : K ≤ M - 1 := by omega
  refine ceil_budget_of_add (by norm_num) hKM ?_
  subst_vars
  have hsub : (5 + e + h - 1 : ℕ) = 4 + e + h := by omega
  rw [hsub]
  nlinarith [he3, hh1]

/-- Odd `a = 2n+1`, `η ∈ {n, n+1}`, `n ≥ 3`: shared core for both
orientations. `K = n+1`, `S ≤ (n-1)*b+M`; the required slack
`ne + (a-2)h - 2a + 1 ≥ 0` holds outright for `h ≥ 2`, and for `h = 1` needs
the extra bound `3 ≤ e` (supplied by each orientation's congruence, in
`odd_budget_eta_n`/`odd_budget_eta_n1` below). -/
theorem odd_budget_eta_n_core {n a e h b M K S : ℕ}
    (hn : 3 ≤ n) (ha : a = 2 * n + 1) (hb : b = a + e) (hM : M = b + h)
    (he : 1 ≤ e) (hh1 : 1 ≤ h) (hK : K = n + 1) (hS : S ≤ (n - 1) * b + M)
    (he1 : h = 1 → 3 ≤ e) :
    K + (M - 1 + S + a - 1) / a ≤ M - 1 := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hn1 : (n' + 1 - 1 : ℕ) = n' := by omega
  rw [hn1] at hS
  have hKM : K ≤ M - 1 := by omega
  refine ceil_budget_of_add (by omega) hKM ?_
  have hworst : M - 1 + S + a * K ≤ M - 1 + (n' * b + M) + a * K := by omega
  refine hworst.trans ?_
  rcases eq_or_ne h 1 with rfl | hne
  · have he3 := he1 rfl
    subst ha hb hM hK
    have hsub : (2 * (n' + 1) + 1 + e + 1 - 1 : ℕ) = 2 * n' + e + 3 := by omega
    rw [hsub]
    nlinarith [he3, hn]
  · have hh2 : 2 ≤ h := by omega
    subst ha hb hM hK
    have hsub : (2 * (n' + 1) + 1 + e + h - 1 : ℕ) = 2 * n' + e + h + 2 := by omega
    rw [hsub]
    nlinarith [he, hh2, hn]

/-- Odd `a = 2n+1`, `η = n`, `n ≥ 3`, forward orientation: `h = 1` forces
`a ∣ 3e+2`, whence `e ≥ 3` since neither `5` nor `8` is a multiple of the
odd `a ≥ 7`. -/
theorem odd_budget_eta_n {n a e h b M K S : ℕ}
    (hn : 3 ≤ n) (ha : a = 2 * n + 1) (hb : b = a + e) (hM : M = b + h)
    (he : 1 ≤ e) (hh1 : 1 ≤ h) (hK : K = n + 1) (hS : S ≤ (n - 1) * b + M)
    (hcong : h = 1 → a ∣ (3 * e + 2)) :
    K + (M - 1 + S + a - 1) / a ≤ M - 1 := by
  apply odd_budget_eta_n_core hn ha hb hM he hh1 hK hS
  intro h1
  have hdvd := hcong h1
  by_contra hlt
  push_neg at hlt
  interval_cases e
  · have h5 : a ≤ 5 := Nat.le_of_dvd (by norm_num) (by norm_num at hdvd ⊢; exact hdvd)
    omega
  · have h8 : a ≤ 8 := Nat.le_of_dvd (by norm_num) (by norm_num at hdvd ⊢; exact hdvd)
    have ha7 : 7 ≤ a := by omega
    interval_cases a
    · exact absurd hdvd (by decide)
    · omega

/-- Odd `a = 2n+1`, `η = n+1`, `n ≥ 3`, reverse orientation: `h = 1` forces
`a ∣ e+2`, whence `e ≥ a-2 ≥ 5` since the smallest positive multiple of `a`
is `a` itself. -/
theorem odd_budget_eta_n1 {n a e h b M K S : ℕ}
    (hn : 3 ≤ n) (ha : a = 2 * n + 1) (hb : b = a + e) (hM : M = b + h)
    (he : 1 ≤ e) (hh1 : 1 ≤ h) (hK : K = n + 1) (hS : S ≤ (n - 1) * b + M)
    (hcong : h = 1 → a ∣ (e + 2)) :
    K + (M - 1 + S + a - 1) / a ≤ M - 1 := by
  apply odd_budget_eta_n_core hn ha hb hM he hh1 hK hS
  intro h1
  have hdvd := hcong h1
  have hle : a ≤ e + 2 := Nat.le_of_dvd (by omega) hdvd
  omega

end Erdos1112.Proof.Short
