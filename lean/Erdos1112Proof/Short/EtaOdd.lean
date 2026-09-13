/- Short paper `lem:eta`, odd `a = 2n+1`: the symmetric η argument.

No SHARP table/lift/staircase machinery. Builds on the generic residue-path
machinery in `Short/ResidueFrame.lean` (`residue_frame_pos_run`,
`residue_frame_neg_run`, `path_K_le`), the generic ceiling/budget bridge in
`Short/EvenBudget.lean` (`ceil_le_iff`, `budget_of_le` — those two lemmas
are `a`-agnostic, not actually even-specific), and the two explicit
exceptional witnesses in `Short/OddSpacing.lean` (`spacing_one`,
`spacing_two`). -/
import Erdos1112Proof.Short.Intervals
import Erdos1112Proof.Short.ResidueFrame
import Erdos1112Proof.Short.EvenBudget
import Erdos1112Proof.Short.OddSpacing
import Erdos1112Proof.Short.OddBudget
import Erdos1112Proof.Short.SharpDefs

namespace Erdos1112.Proof.Short

open Erdos1112.Proof

/-! ### Odd-`a` `K`-bound arithmetic (paper: "Furthermore
`t-1+⌊2n/t⌋=n+1` forces `t∈{2,n}`, since `(t-2)(t-n)<0` for `2<t<n`"). -/

/-- For `3 ≤ t ≤ n-1`, `K = t-1+⌊2n/t⌋ ≤ n` (strictly better than the
general `⌈a/2⌉ = n+1` bound from `path_K_le`, away from the endpoints). -/
theorem odd_path_K_bound {n t : ℕ} (ht3 : 3 ≤ t) (htn : t ≤ n - 1) :
    t - 1 + (2 * n) / t ≤ n := by
  have ht0 : 0 < t := by omega
  have hkey : 2 * n < (n - t + 2) * t := by
    have h1a : (1 : ℤ) ≤ (t : ℤ) - 2 := by omega
    have h1b : (1 : ℤ) ≤ (n : ℤ) - t := by omega
    have h1 : (1 : ℤ) ≤ ((t : ℤ) - 2) * ((n : ℤ) - t) := by
      nlinarith [mul_le_mul h1a h1b (by omega) (by omega)]
    have hcast : ((n - t + 2 : ℕ) : ℤ) = (n : ℤ) - t + 2 := by
      have hh : t ≤ n := by omega
      push_cast [Nat.cast_sub hh]; ring
    have hgoal : (2 * n : ℤ) < ((n - t + 2 : ℕ) : ℤ) * t := by rw [hcast]; nlinarith [h1]
    exact_mod_cast hgoal
  have hdiv : 2 * n / t < n - t + 2 := (Nat.div_lt_iff_lt_mul ht0).mpr hkey
  omega

/-- A maximal `K = n+1` (`2 ≤ t ≤ n`) forces `t = 2` or `t = n`. -/
theorem odd_t_classification {n t : ℕ} (ht2 : 2 ≤ t) (htn : t ≤ n)
    (hmax : t - 1 + (2 * n) / t = n + 1) : t = 2 ∨ t = n := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h2, hnn⟩ := hcon
  have ht3 : 3 ≤ t := by omega
  have htn1 : t ≤ n - 1 := by omega
  have := odd_path_K_bound ht3 htn1
  omega

/-! ### Small arithmetic facts about the path parameters `t, Z, r, K`,
factored out as standalone lemmas (rather than inlined) so that `omega`
does not have to wade through the large ambient context of the main
`eta_odd` proof. -/

/-- `r = a-1-t*Z` is the remainder `(a-1) % t`, hence `r < t`. -/
theorem odd_r_lt_t {a t Z r : ℕ} (ht0 : 0 < t) (hZ : Z = (a - 1) / t)
    (hr : r = a - 1 - t * Z) : r < t := by
  have h1 := Nat.div_add_mod (a - 1) t
  have h2 := Nat.mod_lt (a - 1) ht0
  rw [← hZ] at h1
  omega

/-- Forward orientation: `S = max((t-1)b+(Z-1)M, r*b+Z*M) ≤ K*M`. -/
theorem odd_pos_S_le_KM {t Z r b M K : ℕ} (hK : K = t - 1 + Z) (hr_lt : r < t) (hbM : b < M) :
    max ((t - 1) * b + (Z - 1) * M) (r * b + Z * M) ≤ K * M := by
  have hb1 : (t - 1) * b + (Z - 1) * M ≤ K * M := by
    have e1 : (t - 1) * b ≤ (t - 1) * M := Nat.mul_le_mul_left _ (by omega)
    have e3 : t - 1 + (Z - 1) ≤ K := by omega
    have e4 : (t - 1 + (Z - 1)) * M ≤ K * M := Nat.mul_le_mul_right _ e3
    have e2 : (t - 1) * M + (Z - 1) * M = (t - 1 + (Z - 1)) * M := by ring
    omega
  have hb2 : r * b + Z * M ≤ K * M := by
    have e1 : r * b ≤ r * M := Nat.mul_le_mul_left _ (by omega)
    have e3 : r + Z ≤ K := by omega
    have e4 : (r + Z) * M ≤ K * M := Nat.mul_le_mul_right _ e3
    have e2 : r * M + Z * M = (r + Z) * M := by ring
    omega
  exact max_le hb1 hb2

/-- The reversed-orientation `ModEq` fact: if `t = a - η` and
`η*b ≡ M (mod a)` then `M + t*b ≡ 0 (mod a)` — the hypothesis
`residue_frame_neg`/`residue_frame_neg_run` need with `p := b, q := M`. -/
theorem odd_neg_modEq {a η b M t : ℕ} (ht : t = a - η) (hηlt : η < a)
    (hηZ : (η : ZMod a) * (b : ZMod a) = (M : ZMod a)) :
    Nat.ModEq a (M + t * b) 0 := by
  haveI : NeZero a := ⟨by omega⟩
  have hcast : ((t : ℕ) : ZMod a) = -(η : ZMod a) := by
    have hc : (t : ZMod a) = (a : ZMod a) - (η : ZMod a) := by
      rw [ht]; push_cast [Nat.cast_sub (le_of_lt hηlt)]; ring
    rw [hc, ZMod.natCast_self]; ring
  have hzero : ((M + t * b : ℕ) : ZMod a) = 0 := by
    push_cast
    rw [hcast]
    linear_combination -hηZ
  rw [Nat.modEq_zero_iff_dvd]
  exact (ZMod.natCast_eq_zero_iff _ a).mp hzero

/-- Reversed orientation: `S = (t-1)b+Z*M ≤ K*M`. -/
theorem odd_neg_S_le_KM {t Z b M K : ℕ} (hK : K = t - 1 + Z) (hbM : b < M) :
    (t - 1) * b + Z * M ≤ K * M := by
  have e1 : (t - 1) * b ≤ (t - 1) * M := Nat.mul_le_mul_left _ (by omega)
  have e4 : (t - 1 + Z) * M ≤ K * M := Nat.mul_le_mul_right _ (by omega)
  have e2 : (t - 1) * M + Z * M = (t - 1 + Z) * M := by ring
  omega

/-! ### `η = 2` exceptional construction (`t=2, Z=n, r=0`, forward). -/

/-- Paper `lem:eta`, `η = 2` case: the `e = h, λ = 0` exceptions `h ∈ {1,2}`
are the explicit `Short/OddSpacing.lean` witnesses; everything else goes
through the generic forward path with `t=2, Z=n, r=0, S=n*M`. -/
theorem eta_odd_eta_eq_two {n b M a t Z r K η : ℕ} (hn2 : 2 ≤ n) (hab : a < b) (hbM : b < M)
    (hdense : M + 2 ≤ a + b)
    (ha_def : a = 2 * n + 1) (ht_def : t = 2) (hZ_def : Z = n) (hr_def : r = 0)
    (hK_def : K = n + 1) (hηeq : η = 2)
    (ha0 : 0 < a) (hcab_symm : Nat.Coprime b a) (hη : (η * b) % a = M % a) :
    SharpTriple a b M := by
  obtain ⟨e, he_def⟩ : ∃ e, b = a + e := ⟨b - a, by omega⟩
  obtain ⟨h, hh_def⟩ : ∃ h, M = b + h := ⟨M - b, by omega⟩
  have hh1 : 1 ≤ h := by clear hη hK_def; omega
  have hh_lt : h < a := by clear hη hK_def; omega
  haveI : NeZero a := ⟨ha0.ne'⟩
  have hηZ : (2 : ZMod a) * (b : ZMod a) = (M : ZMod a) := by
    have hh := (ZMod.natCast_eq_natCast_iff (η * b) M a).mpr hη
    push_cast at hh
    rw [hηeq] at hh
    push_cast at hh
    convert hh using 2
  obtain ⟨lam, hlam⟩ : ∃ lam, e = h + lam * a := by
    have heZ : (e : ZMod a) = (h : ZMod a) := by
      have hcast_b : (b : ZMod a) = (a : ZMod a) + (e : ZMod a) := by rw [he_def]; push_cast; ring
      have hcast_M : (M : ZMod a) = (a : ZMod a) + (e : ZMod a) + (h : ZMod a) := by
        rw [hh_def, he_def]; push_cast; ring
      rw [hcast_b, hcast_M, ZMod.natCast_self] at hηZ
      linear_combination hηZ
    have hemod : e % a = h % a := (ZMod.natCast_eq_natCast_iff e h a).mp heZ
    have hhmod : h % a = h := Nat.mod_eq_of_lt hh_lt
    refine ⟨e / a, ?_⟩
    have hdm := Nat.div_add_mod e a
    have hcomm : e / a * a = a * (e / a) := Nat.mul_comm _ _
    clear hη hK_def hηZ
    omega
  by_cases hspecial : lam = 0 ∧ h ≤ 2
  · obtain ⟨hlam0, hh2⟩ := hspecial
    subst hlam0
    clear hK_def
    interval_cases h
    · have hbval : b = 2 * n + 2 := by omega
      have hMval : M = 2 * n + 3 := by omega
      have hres := spacing_one n hn2
      rw [ha_def, hbval, hMval]
      exact hres
    · have hbval : b = 2 * n + 3 := by omega
      have hMval : M = 2 * n + 5 := by omega
      have hres := spacing_two n hn2
      rw [ha_def, hbval, hMval]
      exact hres
  · push_neg at hspecial
    have hcase : 1 ≤ lam ∨ 3 ≤ h := by
      rcases Nat.eq_zero_or_pos lam with h0 | h1
      · right; exact hspecial h0
      · left; omega
    have hS_le : max ((t - 1) * b + (Z - 1) * M) (r * b + Z * M) = n * M := by
      rw [ht_def, hZ_def, hr_def]
      simp only [Nat.zero_mul, Nat.zero_add]
      have hle : (2 - 1) * b + (n - 1) * M ≤ n * M := by
        have hnM : (n - 1) * M + M = n * M := by
          have hn1 : n - 1 + 1 = n := by omega
          nlinarith [hn1]
        have hb1 : b ≤ M := hbM.le
        omega
      omega
    set S := n * M with hS_def'
    set x := (M - 1 + S + a - 1) / a with hx_def
    have hbudget : M - 1 + S ≤ a * x := (ceil_le_iff ha0).mp (le_refl _)
    have hcardb : K + x ≤ M - 1 :=
      odd_budget_eta_two hn2 ha_def he_def hh_def hh1 hcase hlam hK_def hS_def'
    have hZ_eq2 : Z = (a - 1) / t := by rw [ht_def, ha_def, hZ_def]; omega
    have hr_eq2 : r = a - 1 - t * Z := by rw [ht_def, hZ_def, ha_def, hr_def]; omega
    have hrun : HasRun (subsetSums (Multiset.replicate (t - 1) b + Multiset.replicate Z M +
        Multiset.replicate x a)) M := by
      apply residue_frame_pos_run ha0 (by omega) hcab_symm (by omega) hZ_eq2 hr_eq2
      · rw [ht_def]
        show Nat.ModEq a M (2 * b)
        rw [hηeq] at hη
        exact hη.symm
      · rw [hS_le]; exact hbudget
    refine ⟨Multiset.replicate (t - 1) b + Multiset.replicate Z M + Multiset.replicate x a,
      ?_, ?_, hrun⟩
    · intro y hy
      rcases Multiset.mem_add.mp hy with hy | hy
      · rcases Multiset.mem_add.mp hy with hy | hy
        · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hy))
        · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hy))
      · exact Or.inl (Multiset.eq_of_mem_replicate hy)
    · have hcard : (Multiset.replicate (t - 1) b + Multiset.replicate Z M +
          Multiset.replicate x a).card = (t - 1) + Z + x := by simp
      rw [hcard]; omega

/-! ### `η = -2` (`η = a-2`) exceptional construction: reversed pair
`(p,q) = (M,b)`, ratio `n` (paper: "reverse `b,M`; the reversed ratio is
`n`"). Two sub-cases: `n ≥ 3` (centered frame `[b, b+(n-1)M]`) and `n = 2`
(`a=5`, bespoke small case). -/

/-- The reversed-pair relation `b ≡ n*M (mod a)` from `η = a-2`. -/
theorem etam2_qtp {a n b M η : ℕ} (hn1 : 1 ≤ n) (ha_def : a = 2 * n + 1) (ha0 : 0 < a)
    (hηeq : η = a - 2) (hηZ : (η : ZMod a) * (b : ZMod a) = (M : ZMod a)) :
    Nat.ModEq a b (n * M) := by
  haveI : NeZero a := ⟨ha0.ne'⟩
  have haeq : ((a - 2 : ℕ) : ZMod a) = (a : ZMod a) - 2 := by
    push_cast [Nat.cast_sub (show 2 ≤ a by omega)]; ring
  rw [hηeq, haeq, ZMod.natCast_self] at hηZ
  have hM2b : (M : ZMod a) = -2 * (b : ZMod a) := by linear_combination -hηZ
  have hn2 : (2 * (n : ZMod a) + 1) = 0 := by
    have h1 : ((a : ℕ) : ZMod a) = ((2 * n + 1 : ℕ) : ZMod a) := by rw [ha_def]
    rw [ZMod.natCast_self] at h1
    push_cast at h1
    linear_combination -h1
  have hbnM : (n : ZMod a) * (M : ZMod a) = (b : ZMod a) := by
    rw [hM2b]
    linear_combination (-(b : ZMod a)) * hn2
  have hcast : ((n * M : ℕ) : ZMod a) = (n : ZMod a) * (M : ZMod a) := by push_cast; ring
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [hcast]; exact hbnM.symm)

/-- `n ≥ 3` centered-frame representatives for `η = -2`: `M^{n-1}, b^2` with
span `[b, b+(n-1)M]`. Only residue `0` needs the non-canonical
representative `M+2b` (all others come from the canonical `n = 2k+j`
decomposition, which is automatically `≥ b`). -/
theorem etam2_hreps {n a b M : ℕ} (hn3 : 3 ≤ n) (ha_def : a = 2 * n + 1)
    (ha0 : 0 < a) (hbM : b < M) (hcaM_symm : Nat.Coprime M a)
    (hqtp : Nat.ModEq a b (n * M)) :
    ∀ c < a, ∃ v ∈ subsetSums (Multiset.replicate (n - 1) M + Multiset.replicate 2 b),
      b ≤ v ∧ v ≤ b + (n - 1) * M ∧ v % a = c := by
  intro c hc
  obtain ⟨w, hwlt, hw⟩ := residue_representative ha0 hcaM_symm c
  by_cases hw0 : w = 0
  · subst hw0
    simp at hw
    have hc' : c % a = c := Nat.mod_eq_of_lt hc
    have hc0 : c = 0 := by omega
    refine ⟨1 * M + 2 * b, ?_, ?_, ?_, ?_⟩
    · exact add_mem_subsetSums_add (replicate_sum_mem M 1 (n - 1) (by omega))
        (replicate_sum_mem b 2 2 (by omega))
    · omega
    · have hstep : (n - 2) * M ≥ M := Nat.le_mul_of_pos_left M (by omega)
      have hexpand : (n - 1) * M = (n - 2) * M + M := by
        have hnn : n - 1 = (n - 2) + 1 := by omega
        rw [hnn]; ring
      omega
    · have heq : Nat.ModEq a (1 * M + 2 * b) (1 * M + 2 * (n * M)) :=
        (hqtp.mul_left 2).add_left (1 * M)
      have heq2 : (1 * M + 2 * (n * M) : ℕ) = (2 * n + 1) * M := by ring
      rw [heq2, ← ha_def] at heq
      have hself : Nat.ModEq a (a * M) 0 := (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right a M)
      have hfin := heq.trans hself
      show (1 * M + 2 * b) % a = c
      rw [hc0]
      simpa [Nat.ModEq] using hfin
  · set j := w % n with hjdef
    set k := w / n with hkdef
    have hwjk : n * k + j = w := by rw [hjdef, hkdef]; exact Nat.div_add_mod w n
    have hjltn : j < n := Nat.mod_lt _ (by omega)
    have hknot : j = 0 → k = 0 → False := by
      intro hj0 hk0
      apply hw0
      rw [hj0, hk0] at hwjk
      simpa using hwjk.symm
    have hkle : k ≤ 2 := by
      by_contra hgt
      push_neg at hgt
      have hh : n * 3 ≤ n * k := Nat.mul_le_mul_left n hgt
      omega
    have hjle2 : k = 2 → j = 0 := by
      intro hkeq
      by_contra hjne
      have hj1 : 1 ≤ j := by omega
      have hh : n * 2 + 1 ≤ n * k + j := by rw [hkeq]; omega
      omega
    refine ⟨j * M + k * b, ?_, ?_, ?_, ?_⟩
    · exact add_mem_subsetSums_add (replicate_sum_mem M j (n - 1) (by omega))
        (replicate_sum_mem b k 2 hkle)
    · rcases Nat.eq_zero_or_pos j with hj0 | hj1
      · have hk1 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with hk0 | hk1
          · exact (hknot hj0 hk0).elim
          · exact hk1
        have hbk : b ≤ k * b := Nat.le_mul_of_pos_left b hk1
        omega
      · have hM : M ≤ j * M := Nat.le_mul_of_pos_left M hj1
        omega
    · rcases eq_or_lt_of_le hkle with hkeq | hklt
      · have hj0 := hjle2 hkeq
        have hkb : k * b = 2 * b := by rw [hkeq]
        rw [hj0, hkb]
        simp only [Nat.zero_mul, Nat.zero_add]
        have hstep : (n - 2) * M ≥ M := Nat.le_mul_of_pos_left M (by omega)
        have hexpand : (n - 1) * M = (n - 2) * M + M := by
          have hnn : n - 1 = (n - 2) + 1 := by omega
          rw [hnn]; ring
        omega
      · have hjM : j * M ≤ (n - 1) * M := Nat.mul_le_mul_right _ (by omega)
        have hkb : k * b ≤ b := by
          have hk1 : k ≤ 1 := by omega
          calc k * b ≤ 1 * b := Nat.mul_le_mul_right _ hk1
            _ = b := by ring
        omega
    · have heq : Nat.ModEq a (j * M + k * b) (j * M + k * (n * M)) :=
        (hqtp.mul_left k).add_left (j * M)
      have heq2 : j * M + k * (n * M) = w * M := by rw [← hwjk]; ring
      rw [heq2] at heq
      have hfin : Nat.ModEq a (j * M + k * b) c := heq.trans hw
      show (j * M + k * b) % a = c
      have hc' : c % a = c := Nat.mod_eq_of_lt hc
      rw [← hc']; exact hfin

theorem eta_odd_eta_am2_ge3 {n b M a η : ℕ} (hn3 : 3 ≤ n) (hab : a < b) (hbM : b < M)
    (hdense : M + 2 ≤ a + b) (ha_def : a = 2 * n + 1) (hηeq : η = a - 2)
    (ha0 : 0 < a) (hcaM_symm : Nat.Coprime M a) (hη : (η * b) % a = M % a) :
    SharpTriple a b M := by
  haveI : NeZero a := ⟨ha0.ne'⟩
  have hηZ : (η : ZMod a) * (b : ZMod a) = (M : ZMod a) := by
    have h := (ZMod.natCast_eq_natCast_iff (η * b) M a).mpr hη
    push_cast at h
    exact h
  have hqtp : Nat.ModEq a b (n * M) := etam2_qtp (by omega) ha_def ha0 hηeq hηZ
  have hreps := etam2_hreps hn3 ha_def ha0 hbM hcaM_symm hqtp
  obtain ⟨e, he_def⟩ : ∃ e, b = a + e := ⟨b - a, by omega⟩
  obtain ⟨h, hh_def⟩ : ∃ h, M = b + h := ⟨M - b, by omega⟩
  have he1 : 1 ≤ e := by clear hη; omega
  have hh1 : 1 ≤ h := by clear hη; omega
  set S := (n - 1) * M with hS_def
  set x := (M - 1 + S + a - 1) / a with hx_def
  have hbudget : M - 1 + S ≤ a * x := (ceil_le_iff ha0).mp (le_refl _)
  have hcardb : (n + 1) + x ≤ M - 1 :=
    odd_budget_eta_neg2_ge3 hn3 ha_def he_def hh_def he1 hh1 rfl hS_def
  have hrun : HasRun (subsetSums (Multiset.replicate (n - 1) M + Multiset.replicate 2 b +
      Multiset.replicate x a)) M := by
    apply centered_frame ha0 (fun c hc => (hreps c hc).imp fun v ⟨hv1, hv2, hv3, hv4⟩ =>
      ⟨hv1, hv2, hv3, hv4⟩)
    omega
  refine ⟨Multiset.replicate (n - 1) M + Multiset.replicate 2 b + Multiset.replicate x a,
    ?_, ?_, hrun⟩
  · intro y hy
    rcases Multiset.mem_add.mp hy with hy | hy
    · rcases Multiset.mem_add.mp hy with hy | hy
      · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hy))
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hy))
    · exact Or.inl (Multiset.eq_of_mem_replicate hy)
  · have hcard : (Multiset.replicate (n - 1) M + Multiset.replicate 2 b +
        Multiset.replicate x a).card = (n - 1) + 2 + x := by simp; omega
    rw [hcard]; omega

/-- `n = 2` (`a = 5`) centered-frame representatives for `η = -2`:
`M^1, b^2` with span `[b, M+2b]`. -/
theorem etam2_eq2_hreps {b M : ℕ} (hbM : b < M) (hcaM_symm : Nat.Coprime M 5)
    (hqtp : Nat.ModEq 5 b (2 * M)) :
    ∀ c < 5, ∃ v ∈ subsetSums (Multiset.replicate 1 M + Multiset.replicate 2 b),
      b ≤ v ∧ v ≤ M + 2 * b ∧ v % 5 = c := by
  intro c hc
  obtain ⟨w, hwlt, hw⟩ := residue_representative (by norm_num) hcaM_symm c
  by_cases hw0 : w = 0
  · subst hw0
    simp at hw
    have hc' : c % 5 = c := Nat.mod_eq_of_lt hc
    have hc0 : c = 0 := by omega
    refine ⟨1 * M + 2 * b, ?_, ?_, ?_, ?_⟩
    · exact add_mem_subsetSums_add (replicate_sum_mem M 1 1 (by omega))
        (replicate_sum_mem b 2 2 (by omega))
    · omega
    · omega
    · have heq : Nat.ModEq 5 (1 * M + 2 * b) (1 * M + 2 * (2 * M)) :=
        (hqtp.mul_left 2).add_left (1 * M)
      have heq2 : (1 * M + 2 * (2 * M) : ℕ) = 5 * M := by ring
      rw [heq2] at heq
      have hself : Nat.ModEq 5 (5 * M) 0 := (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_right 5 M)
      have hfin := heq.trans hself
      show (1 * M + 2 * b) % 5 = c
      rw [hc0]
      simpa [Nat.ModEq] using hfin
  · set j := w % 2 with hjdef
    set k := w / 2 with hkdef
    have hwjk : 2 * k + j = w := by rw [hjdef, hkdef]; exact Nat.div_add_mod w 2
    have hjlt2 : j < 2 := Nat.mod_lt _ (by omega)
    have hknot : j = 0 → k = 0 → False := by
      intro hj0 hk0
      apply hw0
      rw [hj0, hk0] at hwjk
      simpa using hwjk.symm
    have hkle : k ≤ 2 := by
      by_contra hgt
      push_neg at hgt
      have hh : 2 * 3 ≤ 2 * k := Nat.mul_le_mul_left 2 hgt
      omega
    have hjle2 : k = 2 → j = 0 := by
      intro hkeq
      by_contra hjne
      have hj1 : 1 ≤ j := by omega
      have hh : 2 * 2 + 1 ≤ 2 * k + j := by rw [hkeq]; omega
      omega
    refine ⟨j * M + k * b, ?_, ?_, ?_, ?_⟩
    · exact add_mem_subsetSums_add (replicate_sum_mem M j 1 (by omega))
        (replicate_sum_mem b k 2 hkle)
    · rcases Nat.eq_zero_or_pos j with hj0 | hj1
      · have hk1 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with hk0 | hk1
          · exact (hknot hj0 hk0).elim
          · exact hk1
        have hbk : b ≤ k * b := Nat.le_mul_of_pos_left b hk1
        omega
      · have hMM : M ≤ j * M := Nat.le_mul_of_pos_left M hj1
        omega
    · rcases Nat.eq_zero_or_pos j with hj0 | hj1
      · have hjM : j * M = 0 := by rw [hj0]; ring
        have hkb : k * b ≤ 2 * b := Nat.mul_le_mul_right _ hkle
        omega
      · have hj1' : j = 1 := by omega
        have hjM : j * M = M := by rw [hj1']; ring
        have hkb : k * b ≤ 2 * b := Nat.mul_le_mul_right _ hkle
        omega
    · have heq : Nat.ModEq 5 (j * M + k * b) (j * M + k * (2 * M)) :=
        (hqtp.mul_left k).add_left (j * M)
      have heq2 : j * M + k * (2 * M) = w * M := by rw [← hwjk]; ring
      rw [heq2] at heq
      have hfin : Nat.ModEq 5 (j * M + k * b) c := heq.trans hw
      show (j * M + k * b) % 5 = c
      have hc' : c % 5 = c := Nat.mod_eq_of_lt hc
      rw [← hc']; exact hfin

theorem eta_odd_eta_am2_eq2 {b M η a : ℕ} (hab : a < b) (hbM : b < M)
    (hdense : M + 2 ≤ a + b) (ha_def : a = 5) (hηeq : η = 3)
    (hcab : Nat.Coprime a b) (hcaM : Nat.Coprime a M) (hcbM : Nat.Coprime b M)
    (hη : (η * b) % a = M % a) :
    SharpTriple a b M := by
  subst ha_def
  have hηZ : (η : ZMod 5) * (b : ZMod 5) = (M : ZMod 5) := by
    have h := (ZMod.natCast_eq_natCast_iff (η * b) M 5).mpr hη
    push_cast at h
    exact h
  have hqtp0 : Nat.ModEq 5 b (2 * M) :=
    etam2_qtp (by norm_num) (by norm_num) (by norm_num) (by omega) hηZ
  obtain ⟨e, he_def⟩ : ∃ e, b = 5 + e := ⟨b - 5, by omega⟩
  obtain ⟨h, hh_def⟩ : ∃ h, M = b + h := ⟨M - b, by omega⟩
  have he1 : 1 ≤ e := by clear hη; omega
  have hh1 : 1 ≤ h := by clear hη; omega
  have hh3 : h ≤ 3 := by clear hη; omega
  have he3 : 3 ≤ e := by
    by_contra hlt
    push_neg at hlt
    have hbmod : (3 * b) % 5 = M % 5 := by rw [← hηeq]; exact hη
    interval_cases e
    · have hb6 : b = 6 := by omega
      have hh2 : h = 2 := by omega
      have hM8 : M = 8 := by omega
      have hgcd : Nat.gcd b M = 2 := by rw [hb6, hM8]; decide
      rw [hcbM] at hgcd
      omega
    · omega
  have hcaM_symm : Nat.Coprime M 5 := hcaM.symm
  have hreps := etam2_eq2_hreps hbM hcaM_symm hqtp0
  set S := M + b with hS_def
  set x := (M - 1 + S + 5 - 1) / 5 with hx_def
  have ha0 : (0 : ℕ) < 5 := by norm_num
  have hbudget : M - 1 + S ≤ 5 * x := (ceil_le_iff ha0).mp (le_refl _)
  have hcardb : 3 + x ≤ M - 1 :=
    odd_budget_eta_neg2_eq2 he_def hh_def he3 hh1 rfl hS_def
  have hrun : HasRun (subsetSums (Multiset.replicate 1 M + Multiset.replicate 2 b +
      Multiset.replicate x 5)) M := by
    apply centered_frame ha0 (fun c hc => (hreps c hc).imp fun v ⟨hv1, hv2, hv3, hv4⟩ =>
      ⟨hv1, hv2, hv3, hv4⟩)
    omega
  refine ⟨Multiset.replicate 1 M + Multiset.replicate 2 b + Multiset.replicate x 5,
    ?_, ?_, hrun⟩
  · intro y hy
    rcases Multiset.mem_add.mp hy with hy | hy
    · rcases Multiset.mem_add.mp hy with hy | hy
      · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hy))
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hy))
    · exact Or.inl (Multiset.eq_of_mem_replicate hy)
  · have hcard : (Multiset.replicate 1 M + Multiset.replicate 2 b +
        Multiset.replicate x 5).card = 1 + 2 + x := by simp; omega
    rw [hcard]; omega

/-! ### `η = n` and `η = n+1` exceptional constructions (`n ≥ 3`). -/

theorem eta_odd_eta_eq_n {n b M a η : ℕ} (hn3 : 3 ≤ n) (hab : a < b) (hbM : b < M)
    (hdense : M + 2 ≤ a + b) (ha_def : a = 2 * n + 1) (hηeq : η = n)
    (ha0 : 0 < a) (hcab_symm : Nat.Coprime b a) (hη : (η * b) % a = M % a) :
    SharpTriple a b M := by
  haveI : NeZero a := ⟨ha0.ne'⟩
  obtain ⟨e, he_def⟩ : ∃ e, b = a + e := ⟨b - a, by omega⟩
  obtain ⟨h, hh_def⟩ : ∃ h, M = b + h := ⟨M - b, by omega⟩
  have he1 : 1 ≤ e := by clear hη; omega
  have hh1 : 1 ≤ h := by clear hη; omega
  have hcong : h = 1 → a ∣ (3 * e + 2) := by
    intro h1
    have hηZ : (η : ZMod a) * (b : ZMod a) = (M : ZMod a) := by
      have hh := (ZMod.natCast_eq_natCast_iff (η * b) M a).mpr hη
      push_cast at hh
      exact hh
    rw [hηeq] at hηZ
    have hbe : (b : ZMod a) = (e : ZMod a) := by
      have hcast2 : ((b : ℕ) : ZMod a) = ((a + e : ℕ) : ZMod a) := by rw [he_def]
      push_cast [ZMod.natCast_self] at hcast2
      simpa using hcast2
    have hMb1 : (M : ZMod a) = (b : ZMod a) + 1 := by
      have hh2 : ((M : ℕ) : ZMod a) = ((b + h : ℕ) : ZMod a) := by rw [hh_def]
      rw [h1] at hh2
      push_cast at hh2
      convert hh2 using 2
    have h2n1 : (2 * (n : ZMod a) + 1) = 0 := by
      have h1' : ((a : ℕ) : ZMod a) = ((2 * n + 1 : ℕ) : ZMod a) := by rw [ha_def]
      rw [ZMod.natCast_self] at h1'
      push_cast at h1'
      linear_combination -h1'
    have hne1 : ((n : ZMod a) - 1) * (e : ZMod a) = 1 := by
      rw [← hbe]
      linear_combination hηZ + hMb1
    have hgoal : (3 * (e : ZMod a) + 2) = 0 := by
      linear_combination (-2) * hne1 + (e : ZMod a) * h2n1
    have hcast : ((3 * e + 2 : ℕ) : ZMod a) = 3 * (e : ZMod a) + 2 := by push_cast; ring
    have hzero : ((3 * e + 2 : ℕ) : ZMod a) = 0 := by rw [hcast]; exact hgoal
    exact (ZMod.natCast_eq_zero_iff _ a).mp hzero
  set Z := (a - 1) / n with hZ_def
  have hZeq : Z = 2 := by
    rw [hZ_def, ha_def]
    have hsub : 2 * n + 1 - 1 = n * 2 := by omega
    rw [hsub, Nat.mul_div_cancel_left 2 (show 0 < n by omega)]
  set r := a - 1 - n * Z with hr_def
  have hreq : r = 0 := by rw [hr_def, hZeq, ha_def]; omega
  set S := max ((n - 1) * b + (Z - 1) * M) (r * b + Z * M) with hS_def
  have hS_le : S ≤ (n - 1) * b + M := by
    rw [hS_def, hZeq, hreq]
    have h1 : (n - 1) * b + (2 - 1) * M = (n - 1) * b + M := by ring
    have h2 : 0 * b + 2 * M ≤ (n - 1) * b + M := by
      have hMn1b : M ≤ (n - 1) * b := by
        have hstep : (n - 2) * b ≥ b := Nat.le_mul_of_pos_left b (by omega)
        have hexp : (n - 1) * b = (n - 2) * b + b := by
          have hnn : n - 1 = (n - 2) + 1 := by omega
          rw [hnn]; ring
        omega
      omega
    omega
  set x := (M - 1 + S + a - 1) / a with hx_def
  have hbudget : M - 1 + S ≤ a * x := (ceil_le_iff ha0).mp (le_refl _)
  have hcardb : (n + 1) + x ≤ M - 1 :=
    odd_budget_eta_n hn3 ha_def he_def hh_def he1 hh1 rfl hS_le hcong
  have hrun : HasRun (subsetSums (Multiset.replicate (n - 1) b + Multiset.replicate Z M +
      Multiset.replicate x a)) M := by
    apply residue_frame_pos_run ha0 (by omega) hcab_symm (by omega) hZ_def hr_def
    · rw [hηeq] at hη; exact hη.symm
    · exact hbudget
  refine ⟨Multiset.replicate (n - 1) b + Multiset.replicate Z M + Multiset.replicate x a,
    ?_, ?_, hrun⟩
  · intro y hy
    rcases Multiset.mem_add.mp hy with hy | hy
    · rcases Multiset.mem_add.mp hy with hy | hy
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hy))
      · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hy))
    · exact Or.inl (Multiset.eq_of_mem_replicate hy)
  · have hcard : (Multiset.replicate (n - 1) b + Multiset.replicate Z M +
        Multiset.replicate x a).card = (n - 1) + Z + x := by simp
    rw [hcard]; omega

theorem eta_odd_eta_eq_n1 {n b M a η : ℕ} (hn3 : 3 ≤ n) (hab : a < b) (hbM : b < M)
    (hdense : M + 2 ≤ a + b) (ha_def : a = 2 * n + 1) (hηeq : η = n + 1)
    (ha0 : 0 < a) (hcab_symm : Nat.Coprime b a) (hcaM_symm : Nat.Coprime M a)
    (hη : (η * b) % a = M % a) :
    SharpTriple a b M := by
  haveI : NeZero a := ⟨ha0.ne'⟩
  have hηZ : (η : ZMod a) * (b : ZMod a) = (M : ZMod a) := by
    have hh := (ZMod.natCast_eq_natCast_iff (η * b) M a).mpr hη
    push_cast at hh
    exact hh
  rw [hηeq] at hηZ
  push_cast at hηZ
  have h2n1 : (2 * (n : ZMod a) + 1) = 0 := by
    have h1' : ((a : ℕ) : ZMod a) = ((2 * n + 1 : ℕ) : ZMod a) := by rw [ha_def]
    rw [ZMod.natCast_self] at h1'
    push_cast at h1'
    linear_combination -h1'
  have hqtpZ : (b : ZMod a) = 2 * (M : ZMod a) := by
    linear_combination 2 * hηZ - (b : ZMod a) * h2n1
  have hqtp : Nat.ModEq a b (2 * M) := by
    have hcast : ((2 * M : ℕ) : ZMod a) = 2 * (M : ZMod a) := by push_cast; ring
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [hcast]; exact hqtpZ)
  obtain ⟨e, he_def⟩ : ∃ e, b = a + e := ⟨b - a, by omega⟩
  obtain ⟨h, hh_def⟩ : ∃ h, M = b + h := ⟨M - b, by omega⟩
  have he1 : 1 ≤ e := by clear hη; omega
  have hh1 : 1 ≤ h := by clear hη; omega
  have hcong : h = 1 → a ∣ (e + 2) := by
    intro h1
    have hbe : (b : ZMod a) = (e : ZMod a) := by
      have hcast2 : ((b : ℕ) : ZMod a) = ((a + e : ℕ) : ZMod a) := by rw [he_def]
      push_cast [ZMod.natCast_self] at hcast2
      simpa using hcast2
    have hMb1 : (M : ZMod a) = (b : ZMod a) + 1 := by
      have hh2 : ((M : ℕ) : ZMod a) = ((b + h : ℕ) : ZMod a) := by rw [hh_def]
      rw [h1] at hh2
      push_cast at hh2
      convert hh2 using 2
    have hne : (n : ZMod a) * (e : ZMod a) = 1 := by
      rw [← hbe]
      linear_combination hηZ + hMb1
    have hgoal : ((e : ZMod a) + 2) = 0 := by
      linear_combination (-2) * hne + (e : ZMod a) * h2n1
    have hcast : ((e + 2 : ℕ) : ZMod a) = (e : ZMod a) + 2 := by push_cast; ring
    have hzero : ((e + 2 : ℕ) : ZMod a) = 0 := by rw [hcast]; exact hgoal
    exact (ZMod.natCast_eq_zero_iff _ a).mp hzero
  set Z := (a - 1) / 2 with hZ_def
  have hZeq : Z = n := by rw [hZ_def, ha_def]; omega
  set r := a - 1 - 2 * Z with hr_def
  have hreq : r = 0 := by rw [hr_def, hZeq, ha_def]; omega
  set S := max ((2 - 1) * M + (Z - 1) * b) (r * M + Z * b) with hS_def
  have hS_le : S ≤ (n - 1) * b + M := by
    rw [hS_def, hZeq, hreq]
    have h1 : (2 - 1) * M + (n - 1) * b = (n - 1) * b + M := by ring
    have h2 : 0 * M + n * b ≤ (n - 1) * b + M := by
      have hexp : n * b = (n - 1) * b + b := by
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        have hs : n' + 1 - 1 = n' := by omega
        rw [hs]; ring
      omega
    omega
  set x := (M - 1 + S + a - 1) / a with hx_def
  have hbudget : M - 1 + S ≤ a * x := (ceil_le_iff ha0).mp (le_refl _)
  have hcardb : (n + 1) + x ≤ M - 1 :=
    odd_budget_eta_n1 hn3 ha_def he_def hh_def he1 hh1 rfl hS_le hcong
  have hrun : HasRun (subsetSums (Multiset.replicate (2 - 1) M + Multiset.replicate Z b +
      Multiset.replicate x a)) M := by
    apply residue_frame_pos_run ha0 (by omega) hcaM_symm (by omega) hZ_def hr_def
    · exact hqtp
    · exact hbudget
  refine ⟨Multiset.replicate (2 - 1) M + Multiset.replicate Z b + Multiset.replicate x a,
    ?_, ?_, hrun⟩
  · intro y hy
    rcases Multiset.mem_add.mp hy with hy | hy
    · rcases Multiset.mem_add.mp hy with hy | hy
      · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hy))
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hy))
    · exact Or.inl (Multiset.eq_of_mem_replicate hy)
  · have hcard : (Multiset.replicate (2 - 1) M + Multiset.replicate Z b +
        Multiset.replicate x a).card = (2 - 1) + Z + x := by simp; omega
    rw [hcard]; omega

/-! ### Assembly: the full odd-`a` symmetric η lemma. -/

/-- **`lem:eta`, odd `a = 2n+1`**: if `2n+1 < b < M` are pairwise coprime,
`M+2 ≤ (2n+1)+b`, and `(2n+1) ∤ b+M`, then some multiset of at most `M-1`
elements from `{2n+1, b, M}` has `M` consecutive subset sums. -/
theorem eta_odd {n b M : Nat} (hn : 1 ≤ n) (hab : 2 * n + 1 < b) (hbM : b < M)
    (hcab : Nat.Coprime (2 * n + 1) b) (hcaM : Nat.Coprime (2 * n + 1) M)
    (hcbM : Nat.Coprime b M) (hdense : M + 2 ≤ (2 * n + 1) + b)
    (hnodiv : ¬ (2 * n + 1) ∣ b + M) : SharpTriple (2 * n + 1) b M := by
  set a := 2 * n + 1 with ha_def
  have ha0 : 0 < a := by omega
  haveI : NeZero a := ⟨ha0.ne'⟩
  have hh_lo : 1 ≤ M - b := by omega
  have hh_hi : M - b < a := by omega
  obtain ⟨η, hηlt, hη⟩ := residue_representative ha0 hcab.symm M
  have hηZ : (η : ZMod a) * (b : ZMod a) = (M : ZMod a) := by
    have h := (ZMod.natCast_eq_natCast_iff (η * b) M a).mpr hη
    push_cast at h
    exact h
  have hη0 : η ≠ 0 := by
    intro h0
    subst h0
    simp at hηZ
    have hdvd : a ∣ M := (ZMod.natCast_eq_zero_iff M a).mp hηZ.symm
    have hg : a ∣ Nat.gcd a M := Nat.dvd_gcd (dvd_refl a) hdvd
    rw [hcaM] at hg
    have := Nat.le_of_dvd (by norm_num) hg
    omega
  have hη1 : η ≠ 1 := by
    intro h1
    subst h1
    simp at hηZ
    have hcast : ((M - b : ℕ) : ZMod a) = (M : ZMod a) - (b : ZMod a) := by
      push_cast [Nat.cast_sub (le_of_lt hbM)]; ring
    have hzero : ((M - b : ℕ) : ZMod a) = 0 := by rw [hcast, ← hηZ]; ring
    have hdvd : a ∣ (M - b) := (ZMod.natCast_eq_zero_iff _ a).mp hzero
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hηam1 : η ≠ a - 1 := by
    intro ham1
    apply hnodiv
    have haeq : ((a - 1 : ℕ) : ZMod a) = (a : ZMod a) - 1 := by
      push_cast [Nat.cast_sub (show 1 ≤ a by omega)]; ring
    rw [ham1, haeq] at hηZ
    rw [ZMod.natCast_self] at hηZ
    have hbM0 : (b : ZMod a) + (M : ZMod a) = 0 := by linear_combination -hηZ
    have hcast : ((b + M : ℕ) : ZMod a) = (b : ZMod a) + (M : ZMod a) := by push_cast; ring
    have hzero : ((b + M : ℕ) : ZMod a) = 0 := by rw [hcast]; exact hbM0
    exact (ZMod.natCast_eq_zero_iff _ a).mp hzero
  have hη2 : 2 ≤ η := by omega
  have hηam2 : η ≤ a - 2 := by omega
  set t := min η (a - η) with ht_def
  have ht2 : 2 ≤ t := by simp only [ht_def]; omega
  have htn : t ≤ n := by simp only [ht_def]; omega
  have hn2 : 2 ≤ n := by omega
  set Z := (a - 1) / t with hZ_def
  set K := t - 1 + Z with hK_def
  have hta : t ≤ a / 2 := by omega
  have hKn1 : K ≤ n + 1 := by
    have := path_K_le ht2 hta hZ_def
    have han : a / 2 = n := by omega
    have han1 : (a + 1) / 2 = n + 1 := by omega
    omega
  obtain ⟨e, he_def⟩ : ∃ e, b = a + e := ⟨b - a, by omega⟩
  obtain ⟨h, hh_def⟩ : ∃ h, M = b + h := ⟨M - b, by omega⟩
  have he1 : 1 ≤ e := by omega
  have hhh1 : 1 ≤ h := by omega
  rcases le_or_gt K n with hKgen | hKexc
  · -- generic case K ≤ n
    rcases le_or_gt η n with hηn | hηn
    · have hteq : t = η := by omega
      set r := a - 1 - t * Z with hr_def'
      have hr_lt : r < t := odd_r_lt_t (by omega) hZ_def hr_def'
      have hS_le : max ((t - 1) * b + (Z - 1) * M) (r * b + Z * M) ≤ K * M :=
        odd_pos_S_le_KM hK_def hr_lt hbM
      set S := max ((t - 1) * b + (Z - 1) * M) (r * b + Z * M) with hS_def
      set x := (M - 1 + S + a - 1) / a with hx_def
      have hbudget : M - 1 + S ≤ a * x := (ceil_le_iff ha0).mp (le_refl _)
      have hcardb : K + x ≤ M - 1 :=
        odd_budget_generic hn2 (n := n) ha_def he_def hh_def he1 hhh1 hKgen hS_le
      have hrun : HasRun (subsetSums (Multiset.replicate (t - 1) b + Multiset.replicate Z M +
          Multiset.replicate x a)) M := by
        apply residue_frame_pos_run ha0 (by omega) hcab.symm (by omega) hZ_def hr_def'
        · rw [hteq]; exact hη.symm
        · exact hbudget
      refine ⟨Multiset.replicate (t - 1) b + Multiset.replicate Z M + Multiset.replicate x a,
        ?_, ?_, hrun⟩
      · intro y hy
        rcases Multiset.mem_add.mp hy with hy | hy
        · rcases Multiset.mem_add.mp hy with hy | hy
          · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hy))
          · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hy))
        · exact Or.inl (Multiset.eq_of_mem_replicate hy)
      · have hcard : (Multiset.replicate (t - 1) b + Multiset.replicate Z M +
            Multiset.replicate x a).card = (t - 1) + Z + x := by simp
        rw [hcard]; omega
    · have hteq : t = a - η := by omega
      have hqtp : Nat.ModEq a (M + t * b) 0 := odd_neg_modEq hteq hηlt hηZ
      have hS_le : (t - 1) * b + Z * M ≤ K * M := odd_neg_S_le_KM hK_def hbM
      set S := (t - 1) * b + Z * M with hS_def
      set x := (M - 1 + S + a - 1) / a with hx_def
      have hbudget : M - 1 + S ≤ a * x := (ceil_le_iff ha0).mp (le_refl _)
      have hcardb : K + x ≤ M - 1 :=
        odd_budget_generic hn2 (n := n) ha_def he_def hh_def he1 hhh1 hKgen hS_le
      have hrun : HasRun (subsetSums (Multiset.replicate (t - 1) b + Multiset.replicate Z M +
          Multiset.replicate x a)) M := by
        apply residue_frame_neg_run ha0 (by omega) hcab.symm (by omega) hZ_def
        · exact hqtp
        · exact hbudget
      refine ⟨Multiset.replicate (t - 1) b + Multiset.replicate Z M + Multiset.replicate x a,
        ?_, ?_, hrun⟩
      · intro y hy
        rcases Multiset.mem_add.mp hy with hy | hy
        · rcases Multiset.mem_add.mp hy with hy | hy
          · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hy))
          · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hy))
        · exact Or.inl (Multiset.eq_of_mem_replicate hy)
      · have hcard : (Multiset.replicate (t - 1) b + Multiset.replicate Z M +
            Multiset.replicate x a).card = (t - 1) + Z + x := by simp
        rw [hcard]; omega
  · -- exceptional case K = n+1
    have hKeq : K = n + 1 := by omega
    have htcase : t = 2 ∨ t = n := odd_t_classification ht2 htn (by
      have hZ2n : (2 * n) / t = Z := by rw [hZ_def, ha_def]; congr 1
      omega)
    rcases htcase with ht2eq | htneq
    · -- t = 2: η = 2 or η = a - 2
      have hetacase : η = 2 ∨ η = a - 2 := by omega
      have hZeqn : Z = n := by rw [hZ_def, ht2eq, ha_def]; omega
      have hreqn : (a - 1 - t * Z) = 0 := by rw [ht2eq, hZeqn, ha_def]; omega
      rcases hetacase with hetaeq | hetaeq
      · exact eta_odd_eta_eq_two hn2 hab hbM hdense ha_def ht2eq hZeqn hreqn hKeq hetaeq
          ha0 hcab.symm hη
      · rcases eq_or_lt_of_le hn2 with hn2eq | hn3
        · have ha5 : a = 5 := by omega
          have hηeq3 : η = 3 := by omega
          exact eta_odd_eta_am2_eq2 hab hbM hdense ha5 hηeq3 hcab hcaM hcbM hη
        · exact eta_odd_eta_am2_ge3 hn3 hab hbM hdense ha_def hetaeq ha0 hcaM.symm hη
    · -- t = n: η = n or η = n+1
      rcases eq_or_lt_of_le hn2 with hn2eq | hn3
      · -- n = 2: coincides with t = 2, redirect to the η = 2 / η = -2 handlers
        have ht2eq : t = 2 := by omega
        have hetacase : η = 2 ∨ η = a - 2 := by omega
        have hZeqn : Z = n := by rw [hZ_def, ht2eq, ha_def]; omega
        have hreqn : (a - 1 - t * Z) = 0 := by rw [ht2eq, hZeqn, ha_def]; omega
        rcases hetacase with hetaeq | hetaeq
        · exact eta_odd_eta_eq_two hn2 hab hbM hdense ha_def ht2eq hZeqn hreqn hKeq hetaeq
            ha0 hcab.symm hη
        · have ha5 : a = 5 := by omega
          have hηeq3 : η = 3 := by omega
          exact eta_odd_eta_am2_eq2 hab hbM hdense ha5 hηeq3 hcab hcaM hcbM hη
      · have hetacase : η = n ∨ η = n + 1 := by omega
        rcases hetacase with hetaeq | hetaeq
        · exact eta_odd_eta_eq_n hn3 hab hbM hdense ha_def hetaeq ha0 hcab.symm hη
        · exact eta_odd_eta_eq_n1 hn3 hab hbM hdense ha_def hetaeq ha0 hcab.symm hcaM.symm hη

end Erdos1112.Proof.Short
