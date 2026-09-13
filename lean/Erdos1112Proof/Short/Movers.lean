/- Short paper Appendix A: the paired movers lemma (`lem:movers`).

No imports of the old SHARP case analysis, tables, or staircase; this file
depends only on `Short/Intervals.lean` (the residue and subset-sum machinery)
and Mathlib. -/
import Erdos1112Proof.Short.Intervals

namespace Erdos1112.Proof.Short

/-- If `a*idx + (r*a)*κ ≤ a*(r*z+x)` with `idx < r = x+1`, then `κ ≤ z`.
This is the arithmetic core used twice in the paired-movers construction:
once to bound the number of `(b,M)`-pairs by `z`, once (with `y` for `z`,
after adding an extra summand) to bound it by `y`. -/
theorem le_of_mul_add_mul_le {a r x z idx κ : ℕ} (ha0 : 0 < a) (hr0 : 0 < r)
    (hxr : x = r - 1) (hstep : a*idx + (r*a)*κ ≤ a*(r*z+x)) : κ ≤ z := by
  by_contra hlt
  push_neg at hlt
  have h2 : (r*a)*(z+1) ≤ (r*a)*κ := Nat.mul_le_mul_left _ hlt
  have hexp : (r*a)*(z+1) = a*(r*z) + a*r := by ring
  have hexp2 : a*(r*z+x) = a*(r*z) + a*x := by ring
  have hlast : a*x < a*r := (Nat.mul_lt_mul_left ha0).mpr (by omega)
  omega

/-- If `w + w' = a` and `w*b ≡ n (mod a)`, then `w'*M ≡ n (mod a)` whenever
`b + M ≡ 0 (mod a)`. This lets the paired-movers construction switch from
`b`-copies to `M`-copies while keeping the same target residue. -/
theorem modEq_swap_of_add_eq {a b M r w w' n : ℕ} (ha : 0 < a) (hr : b + M = r * a)
    (hww' : w + w' = a) (hwmod : (w*b) % a = n % a) :
    (w'*M) % a = n % a := by
  haveI : NeZero a := ⟨ha.ne'⟩
  have h1 : (w' : ZMod a) = -(w : ZMod a) := by
    have hh : ((w+w' : ℕ) : ZMod a) = ((a:ℕ) : ZMod a) := by exact_mod_cast congrArg _ hww'
    simp at hh
    linear_combination hh
  have h2 : (M : ZMod a) = -(b : ZMod a) := by
    have hh : ((b+M:ℕ) : ZMod a) = ((r*a:ℕ) : ZMod a) := by exact_mod_cast congrArg _ hr
    push_cast at hh
    simp at hh
    linear_combination hh
  have h3 : ((w*b:ℕ) : ZMod a) = ((n:ℕ) : ZMod a) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hwmod
  have h4 : ((w'*M:ℕ) : ZMod a) = ((n:ℕ):ZMod a) := by
    push_cast
    rw [h1, h2]
    push_cast at h3
    linear_combination h3
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h4

/-- The construction engine of the paired movers lemma: given the two
budget inequalities `mover-y`/`mover-z` from the paper (phrased with
`L = max (p*b) (q*M)`, `p+q=a-1`), the multiset `x`-copies-of-`a` +
`y`-copies-of-`b` + `z`-copies-of-`M` has a run of length `M`. -/
theorem hasRun_of_moverBounds {a b M r x y z p q : ℕ} (ha : 0 < a)
    (hco : Nat.Coprime a b) (hr : b + M = r * a) (hr0 : 0 < r) (hpq : p + q = a - 1)
    (hxr : x = r - 1)
    (hmy : max (p*b) (q*M) + M - 1 + p*M ≤ a*(r*y+x))
    (hmz : max (p*b) (q*M) + M - 1 + q*b ≤ a*(r*z+x)) :
    HasRun (subsetSums ((Multiset.replicate x a + Multiset.replicate y b) +
      Multiset.replicate z M)) M := by
  refine ⟨max (p*b) (q*M), fun i _ => ?_⟩
  set L := max (p*b) (q*M) with hL_def
  obtain ⟨w, hwlt, hwmod⟩ := residue_representative ha hco.symm (L+i)
  by_cases hwp : w ≤ p
  · have hnwb : w*b ≤ L+i := by
      have h1 : p*b ≤ L := le_max_left _ _
      have h2 : w*b ≤ p*b := Nat.mul_le_mul_right _ hwp
      omega
    have hdvd : a ∣ (L+i) - w*b := (Nat.modEq_iff_dvd' hnwb).mp hwmod
    obtain ⟨s, hs_eq⟩ := hdvd
    have hLi_eq : L+i = w*b + a*s := by omega
    have hs_split : s % r + r*(s/r) = s := Nat.mod_add_div s r
    set κ := s / r with hκ_def
    set idx := s % r with hidx_def
    have hidx_lt : idx < r := Nat.mod_lt _ hr0
    have hn_eq : L+i = w*b + a*idx + (r*a)*κ := by
      have hexp : a*s = a*idx + (r*a)*κ := by
        have heq2 : a*s = a*(idx+r*κ) := by rw [hs_split]
        rw [heq2]; ring
      omega
    have hi_le : idx ≤ x := by omega
    have hstepz : a*idx + (r*a)*κ ≤ a*(r*z+x) := by
      have hbound : L+M-1 ≤ a*(r*z+x) := by omega
      omega
    have hkz : κ ≤ z := le_of_mul_add_mul_le ha hr0 hxr hstepz
    have hn_eq2 : (L+i) + w*M = a*idx + (r*a)*(w+κ) := by
      linear_combination hn_eq + w*hr
    have hstepy : a*idx + (r*a)*(w+κ) ≤ a*(r*y+x) := by
      have hh : w*M ≤ p*M := Nat.mul_le_mul_right M hwp
      have hle1 : (L+i) + w*M ≤ (L+M-1) + p*M := by omega
      omega
    have hwky : w+κ ≤ y := le_of_mul_add_mul_le ha hr0 hxr hstepy
    have h1 : a*idx ∈ subsetSums (Multiset.replicate x a) := by
      have := replicate_sum_mem a idx x hi_le
      rwa [mul_comm] at this
    have h2 : (w+κ)*b ∈ subsetSums (Multiset.replicate y b) := replicate_sum_mem b (w+κ) y hwky
    have h3 : κ*M ∈ subsetSums (Multiset.replicate z M) := replicate_sum_mem M κ z hkz
    have h12 := add_mem_subsetSums_add h1 h2
    have h123 := add_mem_subsetSums_add h12 h3
    have heq : L+i = a*idx + (w+κ)*b + κ*M := by
      linear_combination hn_eq - κ*hr
    rwa [heq]
  · push_neg at hwp
    set w' := a - w with hw'_def
    have hww' : w + w' = a := by omega
    have hw'q : w' ≤ q := by omega
    have hw'mod : (w'*M) % a = (L+i) % a := modEq_swap_of_add_eq ha hr hww' hwmod
    have hnw'M : w'*M ≤ L+i := by
      have h1 : q*M ≤ L := le_max_right _ _
      have h2 : w'*M ≤ q*M := Nat.mul_le_mul_right _ hw'q
      omega
    have hdvd : a ∣ (L+i) - w'*M := (Nat.modEq_iff_dvd' hnw'M).mp hw'mod
    obtain ⟨s, hs_eq⟩ := hdvd
    have hLi_eq : L+i = w'*M + a*s := by omega
    have hs_split : s % r + r*(s/r) = s := Nat.mod_add_div s r
    set κ := s / r with hκ_def
    set idx := s % r with hidx_def
    have hidx_lt : idx < r := Nat.mod_lt _ hr0
    have hn_eq : L+i = w'*M + a*idx + (r*a)*κ := by
      have hexp : a*s = a*idx + (r*a)*κ := by
        have heq2 : a*s = a*(idx+r*κ) := by rw [hs_split]
        rw [heq2]; ring
      omega
    have hi_le : idx ≤ x := by omega
    have hstepy : a*idx + (r*a)*κ ≤ a*(r*y+x) := by
      have hbound : L+M-1 ≤ a*(r*y+x) := by omega
      omega
    have hky : κ ≤ y := le_of_mul_add_mul_le ha hr0 hxr hstepy
    have hn_eq2 : (L+i) + w'*b = a*idx + (r*a)*(w'+κ) := by
      linear_combination hn_eq + w'*hr
    have hstepz : a*idx + (r*a)*(w'+κ) ≤ a*(r*z+x) := by
      have hh : w'*b ≤ q*b := Nat.mul_le_mul_right b hw'q
      have hle1 : (L+i) + w'*b ≤ (L+M-1) + q*b := by omega
      omega
    have hw'kz : w'+κ ≤ z := le_of_mul_add_mul_le ha hr0 hxr hstepz
    have h1 : a*idx ∈ subsetSums (Multiset.replicate x a) := by
      have := replicate_sum_mem a idx x hi_le
      rwa [mul_comm] at this
    have h2 : κ*b ∈ subsetSums (Multiset.replicate y b) := replicate_sum_mem b κ y hky
    have h3 : (w'+κ)*M ∈ subsetSums (Multiset.replicate z M) := replicate_sum_mem M (w'+κ) z hw'kz
    have h12 := add_mem_subsetSums_add h1 h2
    have h123 := add_mem_subsetSums_add h12 h3
    have heq : L+i = a*idx + κ*b + (w'+κ)*M := by
      linear_combination hn_eq - κ*hr
    rwa [heq]

/-- Auxiliary arithmetic for the hard sub-case of `mover-z` (the "D-slack"
computation in the paper, `a` even): if `z` is the floor of `((x+1)*w+τ)/2`
then `z ≥ w`. Kept as a standalone lemma (rather than inlined) so `nlinarith`
does not choke on the large ambient context of the main proof. -/
theorem dslack_z_ge_w {w x τ z n : ℕ} (hx2 : 2 ≤ x) (hτ1 : 1 ≤ τ) (hw1 : 1 ≤ w)
    (hn : n = (x+1)*w + τ) (hz : z = n/2) : w ≤ z := by
  have hzlo : 2*z ≤ n := by rw [hz]; omega
  have hzhi : n ≤ 2*z+1 := by rw [hz]; omega
  nlinarith [Nat.mul_le_mul_left w hx2]

/-- If in addition `τ = 1`, the floor jumps all the way to `z ≥ w+1`;
used to rule out `τ = 1` in the `z = w` branch. -/
theorem dslack_tau_one_forces {w x z n : ℕ} (hx2 : 2 ≤ x) (hw1 : 1 ≤ w)
    (hn : n = (x+1)*w + 1) (hz : z = n/2) : w+1 ≤ z := by
  have hzlo : 2*z ≤ n := by rw [hz]; omega
  have hzhi : n ≤ 2*z+1 := by rw [hz]; omega
  nlinarith [Nat.mul_le_mul_right w (show 1 ≤ x - 1 from by omega), Nat.sub_add_cancel hx2]

/-- The D-slack inequality itself, case `z ≥ w+1`. -/
theorem dslack_caseA {w x τ z b : ℕ} (hτ1 : 1 ≤ τ) (hw1 : 1 ≤ w)
    (hbeq : b + τ = (w+1)*(x+1)) (hzA : w+1 ≤ z) :
    (2*w+1)*b + ((w+1)*(x+1)+τ) ≤ (2*w+2)*(x+1)*z + (2*w+2)*x + 1 := by
  nlinarith [Nat.mul_le_mul_left ((2*w+2)*(x+1)) hzA, sq_nonneg w, sq_nonneg x]

/-- The D-slack inequality, case `z = w` (needs `τ ≥ 2`). -/
theorem dslack_caseB {w x τ z b : ℕ} (hx2 : 2 ≤ x) (hτ2 : 2 ≤ τ) (hw1 : 1 ≤ w)
    (hbeq : b + τ = (w+1)*(x+1)) (hzB : z = w) :
    (2*w+1)*b + ((w+1)*(x+1)+τ) ≤ (2*w+2)*(x+1)*z + (2*w+2)*x + 1 := by
  rw [hzB]
  nlinarith [sq_nonneg w, sq_nonneg x, Nat.mul_le_mul_left w hx2]

/-- **Paired movers** (paper `lem:movers`). If `3 ≤ a < b < M`, `gcd(a,b)=1`,
and `b+M = r*a`, then for `x = r-1`, `y = ⌈(M-r)/2⌉`, `z = ⌊(M-r)/2⌋`,
the multiset `a^x, b^y, M^z` has `M` consecutive subset sums, using
`x+y+z = M-1` elements. -/
theorem paired_movers {a b M r : ℕ} (ha : 3 ≤ a) (hab : a < b) (hbM : b < M)
    (hco : Nat.Coprime a b) (hr : b + M = r * a) :
    HasRun (subsetSums ((Multiset.replicate (r-1) a +
      Multiset.replicate ((M-r+1)/2) b) + Multiset.replicate ((M-r)/2) M)) M ∧
    (r-1) + (M-r+1)/2 + (M-r)/2 = M - 1 := by
  have hr3 : 3 ≤ r := by by_contra h; push_neg at h; interval_cases r <;> omega
  have key1 : a + r ≤ M + 1 := by
    nlinarith [mul_le_mul (show 2 ≤ a from by omega) (show 2 ≤ r from by omega)
      (by omega : (0:ℕ) ≤ 2) (by omega : (0:ℕ) ≤ a)]
  have har1 : a * (r - 1) = a*r - a := by rw [Nat.mul_sub_one]
  have key2 : M + 1 ≤ a * (r-1) := by
    rw [har1]
    have hcomm : a*r = r*a := Nat.mul_comm a r
    omega
  set p := a / 2 with hp_def
  set q := (a-1) / 2 with hq_def
  set x := r - 1 with hx_def
  set y := (M - r + 1)/2 with hy_def
  set z := (M - r)/2 with hz_def
  have hpq : p + q = a - 1 := by simp only [hp_def, hq_def]; omega
  have hMr : r < M := by omega
  have hpy : p ≤ y := by apply Nat.div_le_div_right; omega
  have hqz : q ≤ z := by apply Nat.div_le_div_right; omega
  have hMx : M ≤ a*x + 1 := by omega
  have hrya : M ≤ r*y + x := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 3 := ⟨r-3, by omega⟩
    obtain ⟨d', hd'⟩ : ∃ d', M - (r'+3) = d' + 2 := ⟨M-(r'+3)-2, by omega⟩
    have h2y : 2*y ≥ d' + 2 := by omega
    have hx' : x = r' + 2 := by omega
    have hM' : M = r' + d' + 5 := by omega
    rw [hx', hM']
    nlinarith [Nat.mul_le_mul_left r' h2y]
  have hL_cases : max (p*b) (q*M) + M - 1 + p*M ≤ a*(r*y+x) ∧
      max (p*b) (q*M) + M - 1 + q*b ≤ a*(r*z+x) := by
    rcases le_total (p*b) (q*M) with hcase | hcase
    · rw [max_eq_right hcase]
      constructor
      · have hpq1 : q*M + p*M = (a-1)*M := by
          have h0 : (p+q)*M = (a-1)*M := by rw [hpq]
          linear_combination h0
        have haM : (a-1)*M + M = a*M := by
          have h1 : a - 1 + 1 = a := by omega
          calc (a-1)*M+M = (a-1+1)*M := by ring
            _ = a*M := by rw [h1]
        have hstep : a*M ≤ a*(r*y+x) := Nat.mul_le_mul_left a hrya
        omega
      · have h1 : q*r*a ≤ z*r*a := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hqz)
        have h2 : a*(r*z+x) = z*r*a + a*x := by ring
        have h3 : q*M + q*b = q*r*a := by
          have h0 : q*(b+M) = q*(r*a) := by rw [hr]
          linear_combination h0
        omega
    · rw [max_eq_left hcase]
      refine ⟨?_, ?_⟩
      · have h1 : p*r*a ≤ y*r*a := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpy)
        have h2 : a*(r*y+x) = y*r*a + a*x := by ring
        have h3 : p*b + p*M = p*r*a := by
          have h0 : p*(b+M) = p*(r*a) := by rw [hr]
          linear_combination h0
        omega
      · -- the hard case: a is forced even, and the D-slack argument applies
        obtain ⟨v, hav, hv2, hpv, hqv⟩ : ∃ v, a = 2*v ∧ 2 ≤ v ∧ p = v ∧ q = v - 1 := by
          have heven : Even a := by
            by_contra hodd
            rw [Nat.not_even_iff_odd] at hodd
            obtain ⟨k, hk⟩ := hodd
            have hpq_eq : p = q := by omega
            have hk1 : 1 ≤ q := by omega
            have hcase' : q*M ≤ q*b := hpq_eq ▸ hcase
            have : M ≤ b := Nat.le_of_mul_le_mul_left hcase' (by omega)
            omega
          obtain ⟨v, hv⟩ := heven
          exact ⟨v, by omega, by omega, by omega, by omega⟩
        obtain ⟨w, hwv⟩ : ∃ w, v = w+1 := ⟨v-1, by omega⟩
        have hw1 : 1 ≤ w := by omega
        have hx2 : 2 ≤ x := by omega
        have h2vr : 2*(v*r) = b + M := by rw [hr, hav]; ring
        have hvr_lt_M : v*r < M := by omega
        obtain ⟨τ, hτ⟩ : ∃ τ, M = v*r + τ := ⟨M - v*r, by omega⟩
        have hτ1 : 1 ≤ τ := by omega
        have hbeq : b + τ = v*r := by omega
        have hxr1 : x + 1 = r := by omega
        have hn : M - r = (x+1)*w + τ := by
          have hvreq : v*r = (w+1)*(x+1) := by rw [hwv, hxr1]
          have hexpand : (w+1)*(x+1) = (x+1)*w + (x+1) := by ring
          omega
        have hzw : w ≤ z := dslack_z_ge_w hx2 hτ1 hw1 hn hz_def
        have hbeq' : b + τ = (w+1)*(x+1) := by rw [← hwv, hxr1]; exact hbeq
        have hDslack : (2*w+1)*b + ((w+1)*(x+1)+τ) ≤
            (2*w+2)*(x+1)*z + (2*w+2)*x + 1 := by
          rcases eq_or_lt_of_le hzw with hzeq | hzlt
          · -- z = w: need τ ≥ 2
            have hτ2 : 2 ≤ τ := by
              by_contra hτ1'
              push_neg at hτ1'
              have hτeq1 : τ = 1 := by omega
              have := dslack_tau_one_forces hx2 hw1 (show M-r = (x+1)*w+1 from by omega) hz_def
              omega
            exact dslack_caseB hx2 hτ2 hw1 hbeq' hzeq.symm
          · exact dslack_caseA hτ1 hw1 hbeq' hzlt
        have hM_eq : M = (w+1)*(x+1) + τ := by rw [hτ, hwv, hxr1]
        have hpq_sum : p*b + q*b = (2*w+1)*b := by
          have hpqw : p + q = 2*w+1 := by omega
          linear_combination b*hpqw
        have haeq : a = 2*w+2 := by omega
        have hareq : a*(r*z+x) = (2*w+2)*(x+1)*z + (2*w+2)*x := by
          rw [haeq, ← hxr1]; ring
        have hLHS : p*b + M - 1 + q*b = (2*w+1)*b + M - 1 := by omega
        have hfinal : (2*w+1)*b + M - 1 ≤ (2*w+2)*(x+1)*z + (2*w+2)*x := by
          have hMeq2 : (2*w+1)*b + M ≤ (2*w+2)*(x+1)*z + (2*w+2)*x + 1 := by
            rw [hM_eq]; exact hDslack
          omega
        rw [hLHS, hareq]
        exact hfinal
  refine ⟨hasRun_of_moverBounds (by omega) hco hr (by omega) hpq hx_def hL_cases.1 hL_cases.2, ?_⟩
  omega

end Erdos1112.Proof.Short
