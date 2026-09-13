/- Short paper `lem:eta`, even `a = 2n`: the symmetric-η case-budget
arithmetic. Verifies `𝓑 = K + ⌈(M-1+S)/a⌉ ≤ M-1` for the maximal-`K`
configurations `η = n-1`, `η = n+1`, and the small even cases `a = 8, 10`.
No SHARP table/lift/staircase machinery; pure ceiling-division arithmetic. -/
import Mathlib

namespace Erdos1112.Proof.Short

/-- The paper's `⌈T/a⌉ = (T+a-1)/a`, bridged to a multiplication bound. -/
lemma ceil_le_iff {a T x : ℕ} (ha : 0 < a) : (T + a - 1) / a ≤ x ↔ T ≤ a * x := by
  constructor
  · intro h
    have h1 := Nat.div_add_mod (T + a - 1) a
    have h2 := Nat.mod_lt (T + a - 1) ha
    have h3 : a * ((T + a - 1) / a) ≤ a * x := Nat.mul_le_mul_left a h
    omega
  · intro h
    by_contra hcon
    push_neg at hcon
    have h1 := Nat.div_add_mod (T + a - 1) a
    have h2 := Nat.mod_lt (T + a - 1) ha
    have h3 : a * (x + 1) ≤ a * ((T + a - 1) / a) := Nat.mul_le_mul_left a hcon
    have h6 : a * (x + 1) = a * x + a := by ring
    omega

/-- The paper's budget `𝓑 = K + ⌈(M-1+S)/a⌉ ≤ M-1`, bridged to the
subtraction-free form `M-1+S ≤ a*(M-1-K)`. -/
theorem budget_iff {a K M S : ℕ} (ha : 0 < a) (hKM : K ≤ M - 1) :
    K + (M - 1 + S + a - 1) / a ≤ M - 1 ↔ M - 1 + S ≤ a * (M - 1 - K) := by
  have hshift : K + (M - 1 + S + a - 1) / a ≤ M - 1 ↔
      (M - 1 + S + a - 1) / a ≤ M - 1 - K := by omega
  rw [hshift]
  exact ceil_le_iff ha

/-- Packaged form of `budget_iff`, taking the subtraction-free inequality
as the hypothesis to discharge. -/
theorem budget_of_le {a K M S : ℕ} (ha : 0 < a) (hKM : K ≤ M - 1)
    (hineq : M - 1 + S ≤ a * (M - 1 - K)) :
    K + (M - 1 + S + a - 1) / a ≤ M - 1 :=
  (budget_iff ha hKM).mpr hineq

/-- Paper `eq:crude-budget`, restricted to even `a = 2n`: for `K ≤ n-1`,
any `S ≤ K*M` with `M ≥ a+1` meets the budget. -/
theorem even_budget_of_le {n K M S : ℕ} (hn : 1 ≤ n) (hK : K ≤ n - 1)
    (hM : 2 * n + 1 ≤ M) (hS : S ≤ K * M) :
    K + (M - 1 + S + 2 * n - 1) / (2 * n) ≤ M - 1 := by
  have ha : 0 < 2 * n := by omega
  have hKM : K ≤ M - 1 := by omega
  apply budget_of_le ha hKM
  have hstep : M - 1 + S ≤ M - 1 + K * M := by omega
  refine hstep.trans ?_
  have hx : (0 : ℤ) ≤ (M : ℤ) - (2 * n + 1) := by omega
  have hy : (0 : ℤ) ≤ (n : ℤ) - 1 - K := by omega
  have hnz : (0 : ℤ) ≤ (n : ℤ) := by positivity
  have hM1 : 1 ≤ M := by omega
  zify [hKM, hM1]
  nlinarith [mul_nonneg hx hy, mul_nonneg hx hnz, mul_nonneg hnz hy]

/-- Paper `eq:eta-even-minus`: for `a = 2n` with `n ≥ 6`, `η = n-1` gives
`K = n`, `S = (n-2)*b+M`, and the budget holds. -/
theorem even_budget_eta_minus {n e h b M : ℕ} (hn : 6 ≤ n) (he : 1 ≤ e)
    (hh1 : 1 ≤ h) (hb : b = 2 * n + e) (hM : M = b + h) :
    n + (M - 1 + ((n - 2) * b + M) + 2 * n - 1) / (2 * n) ≤ M - 1 := by
  have ha : 0 < 2 * n := by omega
  have hKM : n ≤ M - 1 := by omega
  apply budget_of_le ha hKM
  have hM1 : 1 ≤ M := by omega
  zify [hKM, hM1, show 2 ≤ n by omega]
  subst hb hM
  push_cast
  nlinarith [mul_nonneg (show (0:ℤ) ≤ (n:ℤ) - 1 from by omega) (show (0:ℤ) ≤ (h:ℤ) - 1 from by omega)]

/-- Paper `eq:eta-even-plus`: for `a = 2n` with `n ≥ 6`, `η = n+1` forces
`h = n`, giving `K = n`, `S = (n-2)*b+2*M`, and the budget holds. -/
theorem even_budget_eta_plus {n e b M : ℕ} (hn : 6 ≤ n) (he : 1 ≤ e)
    (hb : b = 2 * n + e) (hM : M = b + n) :
    n + (M - 1 + ((n - 2) * b + 2 * M) + 2 * n - 1) / (2 * n) ≤ M - 1 := by
  have ha : 0 < 2 * n := by omega
  have hKM : n ≤ M - 1 := by omega
  apply budget_of_le ha hKM
  have hM1 : 1 ≤ M := by omega
  zify [hKM, hM1, show 2 ≤ n by omega]
  subst hb hM
  push_cast
  nlinarith [mul_nonneg (show (0:ℤ) ≤ (n:ℤ) - 1 from by omega) (show (0:ℤ) ≤ (e:ℤ) - 1 from by omega)]

/-- Paper's `a = 8`, `η = 3` case: `K = 4`, `S = b+2*M`, and the budget
holds (slack `4*e+5*h-7 > 0`). -/
theorem even_budget_a8_eta3 {e h b M : ℕ} (he : 1 ≤ e) (hh1 : 1 ≤ h)
    (hb : b = 8 + e) (hM : M = b + h) :
    4 + (M - 1 + (b + 2 * M) + 8 - 1) / 8 ≤ M - 1 := by
  have ha : (0:ℕ) < 8 := by omega
  have hKM : 4 ≤ M - 1 := by omega
  apply budget_of_le ha hKM
  have hM1 : 1 ≤ M := by omega
  zify [hKM, hM1]
  subst hb hM
  push_cast
  omega

/-- Paper's `a = 8`, `η = 5` case: forces `h = 4`, `K = 4`, `S = 2*b+2*M`,
and the budget holds (slack `3*e+5*h-15 > 0`). -/
theorem even_budget_a8_eta5 {e b M : ℕ} (he : 1 ≤ e)
    (hb : b = 8 + e) (hM : M = b + 4) :
    4 + (M - 1 + (2 * b + 2 * M) + 8 - 1) / 8 ≤ M - 1 := by
  have ha : (0:ℕ) < 8 := by omega
  have hKM : 4 ≤ M - 1 := by omega
  apply budget_of_le ha hKM
  have hM1 : 1 ≤ M := by omega
  zify [hKM, hM1]
  subst hb hM
  push_cast
  omega

/-- Paper's `a = 10`, ratio-`3` case: `K = 5`, `S ≤ 2*b+2*M`, and the
budget holds (slack `5*e+7*h-9 > 0`). -/
theorem even_budget_a10_ratio3 {e h b M : ℕ} (he : 1 ≤ e) (hh1 : 1 ≤ h)
    (hb : b = 10 + e) (hM : M = b + h) :
    5 + (M - 1 + (2 * b + 2 * M) + 10 - 1) / 10 ≤ M - 1 := by
  have ha : (0:ℕ) < 10 := by omega
  have hKM : 5 ≤ M - 1 := by omega
  apply budget_of_le ha hKM
  have hM1 : 1 ≤ M := by omega
  zify [hKM, hM1]
  subst hb hM
  push_cast
  omega

/-- Paper's `t-1+⌊(a-1)/t⌋ ≤ n-1` bound, `a = 2n`: the concave-quadratic
estimate `(t-3)*(n-t-2) ≥ 0` on `3 ≤ t ≤ n-2` shows `K(t)` is not maximal
away from the endpoints. -/
theorem path_K_bound {n t : ℕ} (hn : 6 ≤ n) (ht3 : 3 ≤ t) (htn : t ≤ n - 2) :
    t - 1 + (2 * n - 1) / t ≤ n - 1 := by
  have ht0 : 0 < t := by omega
  have hkey : 2 * n - 1 < (n - t + 1) * t := by
    have h1 : (0 : ℤ) ≤ ((t : ℤ) - 3) * ((n : ℤ) - t - 2) := by
      apply mul_nonneg <;> omega
    zify [show t ≤ n from by omega, show 1 ≤ 2 * n from by omega]
    nlinarith [h1]
  have hdiv : (2 * n - 1) / t < n - t + 1 := (Nat.div_lt_iff_lt_mul ht0).mpr hkey
  omega

/-- Paper's path-combinatoric classification: for `a = 2n ≥ 12`, a maximal
`K = n` among `2 ≤ t ≤ n` forces `t ∈ {2, n-1, n}`. -/
theorem path_t_classification {n t : ℕ} (hn : 6 ≤ n) (ht2 : 2 ≤ t) (htn : t ≤ n)
    (hmax : t - 1 + (2 * n - 1) / t = n) : t = 2 ∨ t = n - 1 ∨ t = n := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h2, hn1, hnn⟩ := hcon
  have ht3 : 3 ≤ t := by omega
  have htn2 : t ≤ n - 2 := by omega
  have := path_K_bound hn ht3 htn2
  omega

/-- `t = 2` is never the ratio of a genuine unit residue mod an even `a`:
`gcd(2, 2n) = 2`. -/
theorem not_coprime_two_even (n : ℕ) : ¬ Nat.Coprime 2 (2 * n) := by
  intro hco
  have hg : Nat.gcd 2 (2 * n) = 2 := Nat.gcd_eq_left ⟨n, rfl⟩
  have hco' : Nat.gcd 2 (2 * n) = 1 := hco
  omega

/-- `t = n` (the self-paired residue `a/2`) is never a unit for `n ≥ 2`:
`gcd(n, 2n) = n`. -/
theorem not_coprime_self_even {n : ℕ} (hn : 2 ≤ n) : ¬ Nat.Coprime n (2 * n) := by
  intro hco
  have hg : Nat.gcd n (2 * n) = n := Nat.gcd_eq_left ⟨2, by ring⟩
  have hco' : Nat.gcd n (2 * n) = 1 := hco
  omega

/-- The remaining case `t = n-1` is a genuine unit ratio, `Coprime (n-1) (2n)`,
exactly for even `n`: this is what forces `n` even in `lem:eta`'s even-`a`
argument. -/
theorem coprime_pred_two_mul_iff {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (n - 1) (2 * n) ↔ Even n := by
  have hcopn : Nat.Coprime (n - 1) n := (Nat.coprime_self_sub_left hn).mpr (Nat.coprime_one_left n)
  rw [Nat.coprime_mul_iff_right]
  constructor
  · rintro ⟨h2, -⟩
    rcases Nat.even_or_odd n with he | ho
    · exact he
    · exact absurd (Nat.coprime_two_right.mp h2) (by
        obtain ⟨k, hk⟩ := ho
        rw [Nat.not_odd_iff_even]
        exact ⟨k, by omega⟩)
  · intro he
    refine ⟨Nat.coprime_two_right.mpr ?_, hcopn⟩
    obtain ⟨k, hk⟩ := he
    exact ⟨k - 1, by omega⟩

end Erdos1112.Proof.Short
