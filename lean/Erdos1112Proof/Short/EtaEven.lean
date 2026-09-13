/- Short paper `lem:eta`, even `a = 2n`: the full symmetric-η argument.

Combines the generic signed residue frames (`Short/ResidueFrame.lean`) with
the even-`a` numeric budget/classification facts (`Short/EvenBudget.lean`,
owned by another agent, read-only here) to prove the even-`a` case of
`lem:eta` outright, including the `a = 4, 6, 8, 10` small cases.

No SHARP table/lift/staircase machinery; only `Sharp/Defs`,
`Short/Intervals`, `Short/ResidueFrame`, `Short/EvenBudget`, and Mathlib. -/
import Erdos1112Proof.Sharp.Defs
import Erdos1112Proof.Short.ResidueFrame
import Erdos1112Proof.Short.EvenBudget

namespace Erdos1112.Proof.Short

open Erdos1112.Proof

/-! ### Small arithmetic helpers -/

/-- The paper's remainder `r = a - 1 - tZ` is `< t` (it is literally
`(a-1) % t`). -/
private lemma r_lt_t {a t Z r : ℕ} (ht : 0 < t) (hZ : Z = (a - 1) / t)
    (hr : r = a - 1 - t * Z) : r < t := by
  have h1 := Nat.div_add_mod (a - 1) t
  have h2 := Nat.mod_lt (a - 1) ht
  have h3 : t * Z = t * ((a - 1) / t) := by rw [hZ]
  omega

/-- Forward `S` is at most `K*M` when `p, q ≤ M`. -/
private lemma S_pos_le_KM {p q M t Z r : ℕ} (hpM : p ≤ M) (hqM : q ≤ M)
    (hrt1 : r ≤ t - 1) :
    max ((t - 1) * p + (Z - 1) * q) (r * p + Z * q) ≤ (t - 1 + Z) * M := by
  have h1 : (t - 1) * p + (Z - 1) * q ≤ (t - 1 + Z) * M := by
    have e1 : (t - 1) * p ≤ (t - 1) * M := Nat.mul_le_mul_left _ hpM
    have e2 : (Z - 1) * q ≤ Z * M := Nat.mul_le_mul (by omega) hqM
    calc (t - 1) * p + (Z - 1) * q ≤ (t - 1) * M + Z * M := Nat.add_le_add e1 e2
    _ = (t - 1 + Z) * M := by ring
  have h2 : r * p + Z * q ≤ (t - 1 + Z) * M := by
    have e1 : r * p ≤ (t - 1) * M := Nat.mul_le_mul hrt1 hpM
    have e2 : Z * q ≤ Z * M := Nat.mul_le_mul_left _ hqM
    calc r * p + Z * q ≤ (t - 1) * M + Z * M := Nat.add_le_add e1 e2
    _ = (t - 1 + Z) * M := by ring
  exact max_le h1 h2

/-- Backward `S` is at most `K*M` when `p, q ≤ M`. -/
private lemma S_neg_le_KM {p q M t Z : ℕ} (hpM : p ≤ M) (hqM : q ≤ M) :
    (t - 1) * p + Z * q ≤ (t - 1 + Z) * M := by
  have e1 : (t - 1) * p ≤ (t - 1) * M := Nat.mul_le_mul_left _ hpM
  have e2 : Z * q ≤ Z * M := Nat.mul_le_mul_left _ hqM
  calc (t - 1) * p + Z * q ≤ (t - 1) * M + Z * M := Nat.add_le_add e1 e2
  _ = (t - 1 + Z) * M := by ring

/-! ### Packaging a frame + budget into a `SharpTriple` -/

/-- Package `residue_frame_pos_run` with an upper bound `Sb` on the true `S`
(rather than `S` itself) into `SharpTriple`, so the numeric `EvenBudget`
lemmas (stated for a convenient `Sb`, not the literal frame maximum) plug in
directly. -/
private lemma sharpTriple_of_pos {a b M p q t Z r Sb : ℕ}
    (hpq : (p = b ∧ q = M) ∨ (p = M ∧ q = b))
    (ha : 0 < a) (hp : 0 < p) (hcop : Nat.Coprime p a) (ht : 0 < t)
    (hZ : Z = (a - 1) / t) (hr : r = a - 1 - t * Z) (hqtp : Nat.ModEq a q (t * p))
    (hSb : max ((t - 1) * p + (Z - 1) * q) (r * p + Z * q) ≤ Sb)
    (hcard : (t - 1) + Z + (M - 1 + Sb + a - 1) / a ≤ M - 1) :
    SharpTriple a b M := by
  have hceil : M - 1 + Sb ≤ a * ((M - 1 + Sb + a - 1) / a) := (ceil_le_iff ha).mp (le_refl _)
  have hbudget : M - 1 + max ((t - 1) * p + (Z - 1) * q) (r * p + Z * q) ≤
      a * ((M - 1 + Sb + a - 1) / a) := by omega
  have hrun := residue_frame_pos_run ha hp hcop ht hZ hr hqtp hbudget
  refine ⟨_, ?_, ?_, hrun⟩
  · intro y hy
    rcases Multiset.mem_add.mp hy with hy | hy
    · rcases Multiset.mem_add.mp hy with hy | hy
      · have hyp : y = p := Multiset.eq_of_mem_replicate hy
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
      · have hyq : y = q := Multiset.eq_of_mem_replicate hy
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    · have hya : y = a := Multiset.eq_of_mem_replicate hy
      omega
  · rw [Multiset.card_add, Multiset.card_add, Multiset.card_replicate, Multiset.card_replicate,
      Multiset.card_replicate]
    omega

/-- Package `residue_frame_neg_run` the same way. -/
private lemma sharpTriple_of_neg {a b M p q t Z Sb : ℕ}
    (hpq : (p = b ∧ q = M) ∨ (p = M ∧ q = b))
    (ha : 0 < a) (hp : 0 < p) (hcop : Nat.Coprime p a) (ht2 : 2 ≤ t)
    (hZ : Z = (a - 1) / t) (hqtp : Nat.ModEq a (q + t * p) 0)
    (hSb : (t - 1) * p + Z * q ≤ Sb)
    (hcard : (t - 1) + Z + (M - 1 + Sb + a - 1) / a ≤ M - 1) :
    SharpTriple a b M := by
  have hceil : M - 1 + Sb ≤ a * ((M - 1 + Sb + a - 1) / a) := (ceil_le_iff ha).mp (le_refl _)
  have hbudget : M - 1 + ((t - 1) * p + Z * q) ≤ a * ((M - 1 + Sb + a - 1) / a) := by omega
  have hrun := residue_frame_neg_run ha hp hcop ht2 hZ hqtp hbudget
  refine ⟨_, ?_, ?_, hrun⟩
  · intro y hy
    rcases Multiset.mem_add.mp hy with hy | hy
    · rcases Multiset.mem_add.mp hy with hy | hy
      · have hyp : y = p := Multiset.eq_of_mem_replicate hy
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
      · have hyq : y = q := Multiset.eq_of_mem_replicate hy
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    · have hya : y = a := Multiset.eq_of_mem_replicate hy
      omega
  · rw [Multiset.card_add, Multiset.card_add, Multiset.card_replicate, Multiset.card_replicate,
      Multiset.card_replicate]
    omega

/-! ### `t` classification for even `a = 2n` -/

/-- Once `t` is a genuine unit ratio in `[2,n]`, it is either `n-1` or lies
strictly inside `[3,n-2]` (`t = 2` and `t = n` are never units mod `2n`). -/
private lemma t_forced_mid_or_n1 {n t : ℕ} (hn : 2 ≤ n) (ht2 : 2 ≤ t) (htn : t ≤ n)
    (htcop : Nat.Coprime t (2 * n)) :
    t = n - 1 ∨ (3 ≤ t ∧ t ≤ n - 2) := by
  rcases (by omega : t = 2 ∨ t = n ∨ t = n - 1 ∨ (3 ≤ t ∧ t ≤ n - 2)) with h | h | h | h
  · exact absurd (h ▸ htcop) (not_coprime_two_even n)
  · exact absurd (h ▸ htcop) (not_coprime_self_even hn)
  · exact Or.inl h
  · exact Or.inr h

/-- `eq:eta-even-minus`'s dominance: the second `max` branch is smaller. -/
private lemma dominance_minus {n b M : ℕ} (hn : 6 ≤ n) (hab : 2 * n < b)
    (hM : M ≤ b + (2 * n - 2)) :
    b + 2 * M ≤ (n - 2) * b + M := by
  have hn' : (6 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hab' : 2 * (n : ℤ) < (b : ℤ) := by exact_mod_cast hab
  have hM' : (M : ℤ) ≤ (b : ℤ) + (2 * (n : ℤ) - 2) := by
    have hcast : ((2 * n - 2 : ℕ) : ℤ) = 2 * (n : ℤ) - 2 := by
      have h2n : (2 : ℕ) ≤ 2 * n := by omega
      push_cast [Nat.cast_sub h2n]; ring
    have hM2 : (M : ℤ) ≤ (b : ℤ) + ((2 * n - 2 : ℕ) : ℤ) := by exact_mod_cast hM
    rwa [hcast] at hM2
  have key : (b : ℤ) + 2 * (M : ℤ) ≤ ((n : ℤ) - 2) * (b : ℤ) + (M : ℤ) := by nlinarith
  have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by
    have h2 : (2 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub h2]; ring
  have hfin : (b : ℤ) + 2 * (M : ℤ) ≤ ((n - 2 : ℕ) : ℤ) * (b : ℤ) + (M : ℤ) := by
    rw [hn2]; exact key
  exact_mod_cast hfin

/-- `eq:eta-even-plus`'s forcing step: with `b, M` odd/even set up so that
`e := b - 2n` is odd, the backward relation `M + (n-1)*b ≡ 0 [MOD 2n]` forces
`h := M - b = n` exactly (using the `h`-range `1 ≤ h ≤ 2n-2`). -/
private lemma h_eq_n_of_backward {n b M e h : ℕ} (hn : 2 ≤ n) (hbe : b = 2 * n + e)
    (hMh : M = b + h) (hodd : Odd e) (hh_ub : h ≤ 2 * n - 2)
    (hqtp : Nat.ModEq (2 * n) (M + (n - 1) * b) 0) : h = n := by
  obtain ⟨m, hm⟩ := hodd
  have step1 : M + (n - 1) * b = e + h + (n - 1) * e + n * (2 * n) := by
    subst hbe hMh
    have h1 : n - 1 + 1 = n := by omega
    nlinarith [h1]
  have step2 : e + h + (n - 1) * e = h + n * e := by
    have h1 : n - 1 + 1 = n := by omega
    nlinarith [h1]
  have step3 : n * e = n + n * (2 * m) := by rw [hm]; ring
  have hcombined : M + (n - 1) * b = h + n + (n * (2 * m) + n * (2 * n)) := by
    rw [step1, step2, step3]; ring
  have hz : Nat.ModEq (2 * n) (M + (n - 1) * b) (h + n) := by
    rw [hcombined]
    have heq2 : n * (2 * m) + n * (2 * n) = (2 * n) * (m + n) := by ring
    rw [heq2]
    have hz0 : Nat.ModEq (2 * n) ((2 * n) * (m + n)) 0 :=
      (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right _ _)
    calc h + n + (2 * n) * (m + n) ≡ h + n + 0 [MOD (2 * n)] := Nat.ModEq.add_left _ hz0
    _ = h + n := by ring
  have hfin : Nat.ModEq (2 * n) (h + n) 0 := hz.symm.trans hqtp
  have hdvd : (2 * n) ∣ (h + n) := (Nat.modEq_zero_iff_dvd).mp hfin
  obtain ⟨k, hk⟩ := hdvd
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp at hk; omega
  · rcases Nat.lt_or_ge k 2 with hk1 | hk1
    · interval_cases k
      omega
    · have hge : 2 * (2 * n) ≤ (2 * n) * k := by
        have h2 : 2 * (2 * n) = (2 * n) * 2 := by ring
        rw [h2]; exact Nat.mul_le_mul_left _ hk1
      omega

/-! ### Forward dispatch -/

/-- Full even-`a` dispatch, forward orientation: `M ≡ t*b [MOD 2n]`. -/
private lemma dispatch_pos {n b M t : ℕ} (hn : 2 ≤ n) (hab : 2 * n < b) (hbM : b < M)
    (hcab : Nat.Coprime (2 * n) b) (hdense : M + 2 ≤ 2 * n + b)
    (ht2 : 2 ≤ t) (htn : t ≤ n) (htcop : Nat.Coprime t (2 * n))
    (hqtp : Nat.ModEq (2 * n) M (t * b)) :
    SharpTriple (2 * n) b M := by
  have hbpos : 0 < b := by omega
  have ha0 : (0:ℕ) < 2 * n := by omega
  have hcba : Nat.Coprime b (2 * n) := hcab.symm
  rcases t_forced_mid_or_n1 hn ht2 htn htcop with htm | ⟨ht3, htn2⟩
  · -- t = n - 1
    have heven : Even n := (coprime_pred_two_mul_iff (by omega : 1 ≤ n)).mp (htm ▸ htcop)
    rcases (by omega : 6 ≤ n ∨ n < 6) with hge6 | hlt6
    · -- n ≥ 6 : paper's `eq:eta-even-minus`
      subst htm
      have hZeq : (2 * n - 1) / (n - 1) = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have hreq : (2 * n - 1) - (n - 1) * 2 = 1 := by omega
      have hbe : b = 2 * n + (b - 2 * n) := by omega
      have hMh : M = b + (M - b) := by omega
      have he1 : 1 ≤ b - 2 * n := by omega
      have hh1 : 1 ≤ M - b := by omega
      have hcard := even_budget_eta_minus hge6 he1 hh1 hbe hMh
      have hdom : b + 2 * M ≤ (n - 2) * b + M := dominance_minus hge6 hab (by omega)
      have hSb : max ((n - 1 - 1) * b + (2 - 1) * M) (1 * b + 2 * M)
          ≤ (n - 2) * b + M := by
        have e1 : (n - 1 - 1) * b + (2 - 1) * M ≤ (n - 2) * b + M := by
          have heq : n - 1 - 1 = n - 2 := by omega
          rw [heq]; omega
        have e2 : 1 * b + 2 * M ≤ (n - 2) * b + M := by omega
        exact max_le e1 e2
      exact sharpTriple_of_pos (Z := 2) (r := 1) (Sb := (n - 2) * b + M) (Or.inl ⟨rfl, rfl⟩) ha0 hbpos hcba
        (by omega : 0 < n - 1) hZeq.symm hreq.symm hqtp hSb (by omega)
    · -- n < 6, even, t = n - 1 ≥ 2 forces n = 4 (the `a = 8`, `η = 3` case)
      have hn4 : n = 4 := by obtain ⟨k, hk⟩ := heven; omega
      subst hn4
      have ht3eq : t = 3 := by omega
      subst ht3eq
      have he1 : 1 ≤ b - 8 := by omega
      have hh1 : 1 ≤ M - b := by omega
      have hbe : b = 8 + (b - 8) := by omega
      have hMh : M = b + (M - b) := by omega
      have hcard := even_budget_a8_eta3 he1 hh1 hbe hMh
      have hSb : max ((3 - 1) * b + (2 - 1) * M) (1 * b + 2 * M) ≤ b + 2 * M := by
        have e1 : (3 - 1) * b + (2 - 1) * M ≤ b + 2 * M := by omega
        have e2 : 1 * b + 2 * M ≤ b + 2 * M := by omega
        exact max_le e1 e2
      exact sharpTriple_of_pos (Z := 2) (r := 1) (Sb := b + 2 * M) (Or.inl ⟨rfl, rfl⟩) ha0 hbpos hcba
        (by norm_num : 0 < 3) (by norm_num : (2:ℕ) = (8 - 1) / 3)
        (by norm_num : (1:ℕ) = 8 - 1 - 3 * 2) hqtp hSb (by norm_num at hcard ⊢; omega)
  · -- 3 ≤ t ≤ n - 2
    rcases (by omega : 6 ≤ n ∨ n < 6) with hge6 | hlt6
    · -- n ≥ 6 : generic budget via `path_K_bound`
      have hK := path_K_bound hge6 ht3 htn2
      have hrbound : (2 * n - 1 - t * ((2 * n - 1) / t)) < t :=
        r_lt_t (a := 2 * n) (show 0 < t by omega) rfl rfl
      have hSb : max ((t - 1) * b + ((2 * n - 1) / t - 1) * M)
          ((2 * n - 1 - t * ((2 * n - 1) / t)) * b + ((2 * n - 1) / t) * M)
          ≤ (t - 1 + (2 * n - 1) / t) * M :=
        S_pos_le_KM (by omega) (le_refl M) (by omega)
      have hcard := even_budget_of_le (show 1 ≤ n by omega) hK (show 2 * n + 1 ≤ M by omega)
        (le_refl ((t - 1 + (2 * n - 1) / t) * M))
      exact sharpTriple_of_pos (Z := (2 * n - 1) / t) (r := 2 * n - 1 - t * ((2 * n - 1) / t))
        (Sb := (t - 1 + (2 * n - 1) / t) * M) (Or.inl ⟨rfl, rfl⟩) ha0 hbpos hcba (by omega)
        rfl rfl hqtp hSb (by omega)
    · -- n < 6, 3 ≤ t ≤ n-2 forces n = 5, t = 3 (the `a = 10` case)
      have hn5 : n = 5 := by omega
      have ht3eq : t = 3 := by omega
      subst hn5; subst ht3eq
      have he1 : 1 ≤ b - 10 := by omega
      have hh1 : 1 ≤ M - b := by omega
      have hbe : b = 10 + (b - 10) := by omega
      have hMh : M = b + (M - b) := by omega
      have hcard := even_budget_a10_ratio3 he1 hh1 hbe hMh
      have hMlt : M < 2 * b := by omega
      have hSb : max ((3 - 1) * b + (3 - 1) * M) (0 * b + 3 * M) ≤ 2 * b + 2 * M := by
        have e1 : (3 - 1) * b + (3 - 1) * M ≤ 2 * b + 2 * M := by omega
        have e2 : 0 * b + 3 * M ≤ 2 * b + 2 * M := by omega
        exact max_le e1 e2
      exact sharpTriple_of_pos (Z := 3) (r := 0) (Sb := 2 * b + 2 * M) (Or.inl ⟨rfl, rfl⟩) ha0 hbpos hcba
        (by norm_num : 0 < 3) (by norm_num : (3:ℕ) = (10 - 1) / 3)
        (by norm_num : (0:ℕ) = 10 - 1 - 3 * 3) hqtp hSb (by norm_num at hcard ⊢; omega)

/-! ### Backward dispatch -/

/-- Full even-`a` dispatch, backward orientation: `M + t*b ≡ 0 [MOD 2n]`. -/
private lemma dispatch_neg {n b M t : ℕ} (hn : 2 ≤ n) (hab : 2 * n < b) (hbM : b < M)
    (hcab : Nat.Coprime (2 * n) b) (hcaM : Nat.Coprime (2 * n) M) (hdense : M + 2 ≤ 2 * n + b)
    (ht2 : 2 ≤ t) (htn : t ≤ n) (htcop : Nat.Coprime t (2 * n))
    (hqtp : Nat.ModEq (2 * n) (M + t * b) 0) :
    SharpTriple (2 * n) b M := by
  have hbpos : 0 < b := by omega
  have ha0 : (0:ℕ) < 2 * n := by omega
  have hcba : Nat.Coprime b (2 * n) := hcab.symm
  have hcMa : Nat.Coprime M (2 * n) := hcaM.symm
  have hb2cop : Nat.Coprime 2 b := Nat.Coprime.coprime_dvd_left ⟨n, rfl⟩ hcab
  have hbodd : Odd b := by
    rw [Nat.coprime_comm] at hb2cop
    exact Nat.coprime_two_right.mp hb2cop
  rcases t_forced_mid_or_n1 hn ht2 htn htcop with htm | ⟨ht3, htn2⟩
  · -- t = n - 1
    have heven : Even n := (coprime_pred_two_mul_iff (by omega : 1 ≤ n)).mp (htm ▸ htcop)
    have heodd : Odd (b - 2 * n) := by
      obtain ⟨k, hk⟩ := hbodd; exact ⟨k - n, by omega⟩
    rcases (by omega : 6 ≤ n ∨ n < 6) with hge6 | hlt6
    · -- n ≥ 6 : paper's `eq:eta-even-plus`
      subst htm
      have hZeq : (2 * n - 1) / (n - 1) = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have hbe : b = 2 * n + (b - 2 * n) := by omega
      have hh_ub : M - b ≤ 2 * n - 2 := by omega
      have hMh0 : M = b + (M - b) := by omega
      have hheq : M - b = n := h_eq_n_of_backward hn hbe hMh0 heodd hh_ub hqtp
      have he1 : 1 ≤ b - 2 * n := by omega
      have hMh : M = b + n := by omega
      have hcard := even_budget_eta_plus hge6 he1 hbe hMh
      have hSb : (n - 1 - 1) * b + 2 * M ≤ (n - 2) * b + 2 * M := by
        have heq : n - 1 - 1 = n - 2 := by omega
        rw [heq]
      exact sharpTriple_of_neg (Z := 2) (Sb := (n - 2) * b + 2 * M) (Or.inl ⟨rfl, rfl⟩) ha0 hbpos
        hcba (by omega : 2 ≤ n - 1) hZeq.symm hqtp hSb (by omega)
    · -- n < 6, even, t = n - 1 ≥ 2 forces n = 4 (the `a = 8`, `η = 5` case, `h = 4`)
      have hn4 : n = 4 := by obtain ⟨k, hk⟩ := heven; omega
      subst hn4
      have ht3eq : t = 3 := by omega
      subst ht3eq
      have hbe : b = 8 + (b - 8) := by omega
      have hh_ub : M - b ≤ 8 - 2 := by omega
      have hMh0 : M = b + (M - b) := by omega
      have hheq : M - b = 4 := h_eq_n_of_backward (by norm_num) hbe hMh0 heodd hh_ub hqtp
      have he1 : 1 ≤ b - 8 := by omega
      have hMh : M = b + 4 := by omega
      have hcard := even_budget_a8_eta5 he1 hbe hMh
      have hSb : (3 - 1) * b + 2 * M ≤ 2 * b + 2 * M := by omega
      exact sharpTriple_of_neg (Z := 2) (Sb := 2 * b + 2 * M) (Or.inl ⟨rfl, rfl⟩) ha0 hbpos hcba
        (by norm_num : 2 ≤ 3) (by norm_num : (2:ℕ) = (8 - 1) / 3) hqtp hSb
        (by norm_num at hcard ⊢; omega)
  · -- 3 ≤ t ≤ n - 2
    rcases (by omega : 6 ≤ n ∨ n < 6) with hge6 | hlt6
    · -- n ≥ 6 : generic budget via `path_K_bound`
      have hK := path_K_bound hge6 ht3 htn2
      have hSb : (t - 1) * b + (2 * n - 1) / t * M ≤ (t - 1 + (2 * n - 1) / t) * M :=
        S_neg_le_KM (by omega) (le_refl M)
      have hcard := even_budget_of_le (show 1 ≤ n by omega) hK (show 2 * n + 1 ≤ M by omega)
        (le_refl ((t - 1 + (2 * n - 1) / t) * M))
      exact sharpTriple_of_neg (Z := (2 * n - 1) / t) (Sb := (t - 1 + (2 * n - 1) / t) * M)
        (Or.inl ⟨rfl, rfl⟩) ha0 hbpos hcba (by omega) rfl hqtp hSb (by omega)
    · -- n < 6, 3 ≤ t ≤ n-2 forces n = 5, t = 3 (the `a = 10` case) : swap to forward
      have hn5 : n = 5 := by omega
      have ht3eq : t = 3 := by omega
      subst hn5; subst ht3eq
      -- swap: M + 3*b ≡ 0 [MOD 10]  ⟹  b ≡ 3*M [MOD 10]
      have hswap : Nat.ModEq 10 b (3 * M) := by
        have h1 : Nat.ModEq 10 (3 * (M + 3 * b)) (3 * 0) := hqtp.mul_left 3
        have h2 : 3 * (M + 3 * b) = 3 * M + 9 * b := by ring
        rw [h2] at h1
        simp only [Nat.mul_zero] at h1
        have h3 : Nat.ModEq 10 (3 * M + 9 * b + b) (0 + b) := h1.add_right b
        have h4 : 3 * M + 9 * b + b = 3 * M + 10 * b := by ring
        rw [h4] at h3
        have h5 : Nat.ModEq 10 (3 * M + 10 * b) (3 * M + 0) :=
          Nat.ModEq.add_left (3 * M) ((Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right 10 b))
        have h6 : Nat.ModEq 10 (3 * M) b := by
          have := h5.symm.trans h3; simpa using this
        exact h6.symm
      have he1 : 1 ≤ b - 10 := by omega
      have hh1 : 1 ≤ M - b := by omega
      have hbe : b = 10 + (b - 10) := by omega
      have hMh : M = b + (M - b) := by omega
      have hcard := even_budget_a10_ratio3 he1 hh1 hbe hMh
      have hMlt : b < 2 * M := by omega
      have hSb : max ((3 - 1) * M + (3 - 1) * b) (0 * M + 3 * b) ≤ 2 * b + 2 * M := by
        have e1 : (3 - 1) * M + (3 - 1) * b ≤ 2 * b + 2 * M := by omega
        have e2 : 0 * M + 3 * b ≤ 2 * b + 2 * M := by omega
        exact max_le e1 e2
      exact sharpTriple_of_pos (Z := 3) (r := 0) (Sb := 2 * b + 2 * M) (Or.inr ⟨rfl, rfl⟩) ha0
        (by omega : 0 < M) hcMa (by norm_num : 0 < 3) (by norm_num : (3:ℕ) = (10 - 1) / 3)
        (by norm_num : (0:ℕ) = 10 - 1 - 3 * 3) hswap hSb (by norm_num at hcard ⊢; omega)

/-! ### The main theorem -/

/-- Paper `lem:eta`, even `a = 2n`: the full symmetric-η argument. -/
theorem eta_even {n b M : Nat} (hn : 2 ≤ n) (hab : 2 * n < b) (hbM : b < M)
    (hcab : Nat.Coprime (2 * n) b) (hcaM : Nat.Coprime (2 * n) M) (hcbM : Nat.Coprime b M)
    (hdense : M + 2 ≤ 2 * n + b) (hnodiv : ¬ (2 * n) ∣ (b + M)) : SharpTriple (2 * n) b M := by
  have ha0 : 0 < 2 * n := by omega
  have hh_lb : 1 ≤ M - b := by omega
  have hh_ub : M - b ≤ 2 * n - 2 := by omega
  obtain ⟨η, hηlt, hη⟩ := residue_representative ha0 hcab.symm M
  have hηM : Nat.ModEq (2 * n) (η * b) M := hη
  have hη0 : η ≠ 0 := by
    intro h0; subst h0
    have hdvd : (2 * n) ∣ M := by
      have hz : M % (2 * n) = 0 := by simpa using hη.symm
      exact Nat.dvd_of_mod_eq_zero hz
    have hd : (2 * n) ∣ Nat.gcd (2 * n) M := Nat.dvd_gcd dvd_rfl hdvd
    rw [hcaM] at hd
    have := Nat.le_of_dvd one_pos hd
    omega
  have hη1 : η ≠ 1 := by
    intro h1; subst h1
    have hbm : Nat.ModEq (2 * n) b M := by simpa using hηM
    have hdvd : (2 * n) ∣ (M - b) := (Nat.modEq_iff_dvd' hbM.le).mp hbm
    obtain ⟨k, hk⟩ := hdvd
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp at hk; omega
    · have hge : 2 * n ≤ (2 * n) * k := Nat.le_mul_of_pos_right _ hk0
      omega
  have hηa1 : η ≠ 2 * n - 1 := by
    intro ha1; subst ha1
    have heq : (2 * n - 1) * b + b = (2 * n) * b := by
      have h1 : 2 * n - 1 + 1 = 2 * n := by omega
      calc (2 * n - 1) * b + b = (2 * n - 1 + 1) * b := by ring
      _ = (2 * n) * b := by rw [h1]
    have h1 : Nat.ModEq (2 * n) ((2 * n - 1) * b + b) ((2 * n) * b) := by rw [heq]
    have h2 : Nat.ModEq (2 * n) ((2 * n) * b) 0 := (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right _ _)
    have h3 : Nat.ModEq (2 * n) (M + b) ((2 * n - 1) * b + b) := (hηM.add_right b).symm
    have h4 : Nat.ModEq (2 * n) (M + b) 0 := (h3.trans h1).trans h2
    exact hnodiv (by have := (Nat.modEq_zero_iff_dvd).mp h4; rwa [add_comm] at this)
  have hηcop : Nat.Coprime η (2 * n) := by
    have hginv : Nat.gcd (2 * n) (η * b) = Nat.gcd (2 * n) M := by
      conv_lhs => rw [Nat.gcd_rec]
      conv_rhs => rw [Nat.gcd_rec]
      rw [hη]
    have hcopηb : Nat.Coprime (2 * n) (η * b) := by
      show Nat.gcd (2 * n) (η * b) = 1
      rw [hginv]; exact hcaM
    exact (Nat.Coprime.coprime_dvd_right (dvd_mul_right η b) hcopηb).symm
  rcases (by omega : η ≤ n ∨ n < η) with hηn | hηn
  · -- forward : `t := η`
    exact dispatch_pos hn hab hbM hcab hdense (by omega) hηn hηcop hηM.symm
  · -- backward : `t := 2n - η`
    have heq : η * b + (2 * n - η) * b = (2 * n) * b := by
      have h1 : η + (2 * n - η) = 2 * n := by omega
      calc η * b + (2 * n - η) * b = (η + (2 * n - η)) * b := by ring
      _ = (2 * n) * b := by rw [h1]
    have hqtp_neg : Nat.ModEq (2 * n) (M + (2 * n - η) * b) 0 := by
      have step1 : Nat.ModEq (2 * n) (M + (2 * n - η) * b) (η * b + (2 * n - η) * b) :=
        (hηM.add_right _).symm
      rw [heq] at step1
      exact step1.trans ((Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right _ _))
    have htcop : Nat.Coprime (2 * n - η) (2 * n) :=
      (Nat.coprime_self_sub_left hηlt.le).mpr hηcop
    exact dispatch_neg hn hab hbM hcab hcaM hdense (by omega) (by omega) htcop hqtp_neg

end Erdos1112.Proof.Short
