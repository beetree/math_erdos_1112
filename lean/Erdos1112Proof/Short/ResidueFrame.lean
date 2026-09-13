/- Short paper `lem:eta`, the generic forward/reversed signed residue path
(paper's `eq:path-data`, `eq:path-positive`, `eq:path-negative`,
`eq:path-cost`, `eq:K-bound`).

Given `a ≥ 1`, a unit `p` mod `a`, and a second value `q` with `q ≡ t*p`
(forward/"positive" orientation) or `q + t*p ≡ 0` (reversed/"negative"
orientation) modulo `a`, this file shows `p^(t-1), q^Z` (for
`Z = (a-1)/t`) has a representative of every residue class mod `a` inside
`[0,S]`, for the paper's two shapes of `S`, and packages this with the
parent's `centered_frame` into direct `HasRun` corollaries. It also proves
the `K = t-1+Z ≤ ⌈a/2⌉` bound (`eq:K-bound`).

This is the *generic* combinatorial core only: no arithmetic case analysis
for the actual triple `(a,b,M)` (that belongs to `Movers.lean` /
`ResiduePath.lean`), and no odd/even spacing constructions
(`OddSpacing.lean`). Depends only on `Short/Intervals.lean` and Mathlib. -/
import Erdos1112Proof.Short.Intervals

namespace Erdos1112.Proof.Short

open Erdos1112.Proof

/-! ### `eq:K-bound`: `K = t - 1 + Z ≤ ⌈a/2⌉`. -/

/-- Paper `eq:K-bound`. For `2 ≤ t ≤ a/2` and `Z = (a-1)/t`,
`K := t - 1 + Z` is at most `⌈a/2⌉ = (a+1)/2`. -/
theorem path_K_le {a t Z : ℕ} (ht2 : 2 ≤ t) (hta : t ≤ a / 2) (hZ : Z = (a - 1) / t) :
    t - 1 + Z ≤ (a + 1) / 2 := by
  have h1 := Nat.div_add_mod (a - 1) t
  have h2 := Nat.mod_lt (a - 1) (show 0 < t by omega)
  have htZ' : t * ((a - 1) / t) ≤ a - 1 := by omega
  have htZ : t * Z ≤ a - 1 := by rw [hZ]; exact htZ'
  have hmc : a / 2 + (a + 1) / 2 = a := by omega
  have hmle : a / 2 ≤ (a + 1) / 2 := by omega
  have ha1 : 1 ≤ a := by omega
  have key : (t : ℤ) - 1 + (Z : ℤ) ≤ ((a + 1) / 2 : ℕ) := by
    have htZi : (t : ℤ) * (Z : ℤ) ≤ (a : ℤ) - 1 := by
      have : ((t * Z : ℕ) : ℤ) ≤ ((a - 1 : ℕ) : ℤ) := by exact_mod_cast htZ
      rwa [Nat.cast_sub ha1] at this
    have hmci : ((a / 2 : ℕ) : ℤ) + (((a + 1) / 2 : ℕ) : ℤ) = (a : ℤ) := by exact_mod_cast hmc
    have hmlei : ((a / 2 : ℕ) : ℤ) ≤ (((a + 1) / 2 : ℕ) : ℤ) := by exact_mod_cast hmle
    have ht2i : (2 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht2
    have htmi : (t : ℤ) ≤ ((a / 2 : ℕ) : ℤ) := by exact_mod_cast hta
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ (t:ℤ) - 2)
        (by linarith : (0:ℤ) ≤ ((a/2:ℕ):ℤ) - (t:ℤ)),
      mul_nonneg (by linarith : (0:ℤ) ≤ (((a+1)/2:ℕ):ℤ) - ((a/2:ℕ):ℤ))
        (by linarith : (0:ℤ) ≤ (t:ℤ) - 1)]
  have ht1 : 1 ≤ t := by omega
  have hcast : (t : ℤ) - 1 + (Z : ℤ) = ((t - 1 + Z : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub ht1]; ring
  rw [hcast] at key
  exact_mod_cast key

/-! ### Forward orientation: `q ≡ t*p [MOD a]`. -/

/-- Paper `eq:path-positive`: with the forward orientation `q ≡ t*p [MOD a]`,
`p^(t-1), q^Z` has a representative of every residue class mod `a`, of size
at most `S = max((t-1)p+(Z-1)q, r*p+Z*q)`. -/
theorem residue_frame_pos {a p q t Z r : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hcop : Nat.Coprime p a) (ht : 0 < t)
    (hZ : Z = (a - 1) / t) (hr : r = a - 1 - t * Z)
    (hqtp : Nat.ModEq a q (t * p)) :
    ∀ c < a, ∃ v ∈ subsetSums (Multiset.replicate (t - 1) p + Multiset.replicate Z q),
      v ≤ max ((t - 1) * p + (Z - 1) * q) (r * p + Z * q) ∧ v % a = c := by
  intro c hc
  obtain ⟨n, hnlt, hn⟩ := residue_representative ha hcop c
  have hnkj : t * (n / t) + n % t = n := Nat.div_add_mod n t
  have hjt : n % t < t := Nat.mod_lt n ht
  set k := n / t with hkdef
  set j := n % t with hjdef
  have hkZ : k ≤ Z := by
    have h1 : n / t ≤ (a - 1) / t := Nat.div_le_div_right (by omega)
    rw [hZ]; exact h1
  have hjr : k = Z → j ≤ r := by
    intro hkeq
    have hteq : t * Z + j = n := by rw [← hkeq]; exact hnkj
    omega
  refine ⟨j * p + k * q, ?_, ?_, ?_⟩
  · exact add_mem_subsetSums_add (replicate_sum_mem p j (t - 1) (by omega))
      (replicate_sum_mem q k Z hkZ)
  · rcases eq_or_lt_of_le hkZ with hkeq | hklt
    · have hjle := hjr hkeq
      have hb : j * p + k * q ≤ r * p + Z * q := by
        rw [hkeq]
        exact Nat.add_le_add (Nat.mul_le_mul_right p hjle) (le_refl (Z * q))
      exact hb.trans (le_max_right _ _)
    · have hkle : k ≤ Z - 1 := by omega
      have hb : j * p + k * q ≤ (t - 1) * p + (Z - 1) * q :=
        Nat.add_le_add (Nat.mul_le_mul_right p (by omega)) (Nat.mul_le_mul_right q hkle)
      exact hb.trans (le_max_left _ _)
  · have step1 : Nat.ModEq a (j * p + k * q) (j * p + k * (t * p)) :=
      (hqtp.mul_left k).add_left (j * p)
    have step2 : j * p + k * (t * p) = n * p := by rw [← hnkj]; ring
    rw [step2] at step1
    have hfin : Nat.ModEq a (j * p + k * q) c := step1.trans hn
    have hc' : c % a = c := Nat.mod_eq_of_lt hc
    show (j * p + k * q) % a = c
    rw [← hc']; exact hfin

/-- `residue_frame_pos` packaged with the parent's `centered_frame`. -/
theorem residue_frame_pos_run {a p q t Z r M x : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hcop : Nat.Coprime p a) (ht : 0 < t)
    (hZ : Z = (a - 1) / t) (hr : r = a - 1 - t * Z) (hqtp : Nat.ModEq a q (t * p))
    (hbudget : M - 1 + max ((t - 1) * p + (Z - 1) * q) (r * p + Z * q) ≤ a * x) :
    HasRun (subsetSums (Multiset.replicate (t - 1) p + Multiset.replicate Z q +
      Multiset.replicate x a)) M :=
  centered_frame ha
    (fun c hc => (residue_frame_pos ha hp hcop ht hZ hr hqtp c hc).imp
      fun v ⟨hv, hvS, hvc⟩ => ⟨hv, Nat.zero_le v, hvS, hvc⟩)
    (by omega)

/-! ### Reversed orientation: `q + t*p ≡ 0 [MOD a]`. -/

/-- Paper `eq:path-negative`: with the reversed orientation `q + t*p ≡ 0
[MOD a]`, `p^(t-1), q^Z` has a representative of every residue class mod
`a`, of size at most `S = (t-1)p + Zq`. -/
theorem residue_frame_neg {a p q t Z : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hcop : Nat.Coprime p a) (ht2 : 2 ≤ t)
    (hZ : Z = (a - 1) / t) (hqtp : Nat.ModEq a (q + t * p) 0) :
    ∀ c < a, ∃ v ∈ subsetSums (Multiset.replicate (t - 1) p + Multiset.replicate Z q),
      v ≤ (t - 1) * p + Z * q ∧ v % a = c := by
  intro c hc
  obtain ⟨n, hnlt, hn⟩ := residue_representative ha hcop c
  by_cases hcase : n < t
  · refine ⟨n * p + 0 * q, ?_, ?_, ?_⟩
    · exact add_mem_subsetSums_add (replicate_sum_mem p n (t - 1) (by omega))
        (replicate_sum_mem q 0 Z (Nat.zero_le Z))
    · have : n * p + 0 * q ≤ (t - 1) * p := by
        simpa using Nat.mul_le_mul_right p (show n ≤ t - 1 by omega)
      omega
    · have hc' : c % a = c := Nat.mod_eq_of_lt hc
      show (n * p + 0 * q) % a = c
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [hn, hc']
  · push_neg at hcase
    obtain ⟨k, j, hkZ, hjt, hjeq⟩ :
        ∃ k j : ℕ, k ≤ Z ∧ j < t ∧ j + a = t * k + n := by
      have hd1 := Nat.div_add_mod (a - n - 1) t
      have hd2 := Nat.mod_lt (a - n - 1) (show 0 < t by omega)
      have he1 := Nat.div_add_mod (a - 1) t
      have he2 := Nat.mod_lt (a - 1) (show 0 < t by omega)
      have hlin : t * ((a - n - 1) / t) < t * ((a - 1) / t) := by omega
      have hD1D2 : (a - n - 1) / t < (a - 1) / t := by
        rcases Nat.lt_or_ge ((a - n - 1) / t) ((a - 1) / t) with h | h
        · exact h
        · exfalso
          have : t * ((a - 1) / t) ≤ t * ((a - n - 1) / t) := Nat.mul_le_mul_left t h
          omega
      have hexpand : t * ((a - n - 1) / t + 1) = t * ((a - n - 1) / t) + t := by ring
      refine ⟨(a - n - 1) / t + 1, t * ((a - n - 1) / t + 1) + n - a, ?_, ?_, ?_⟩
      · rw [hZ]; omega
      · omega
      · omega
    refine ⟨j * p + k * q, ?_, ?_, ?_⟩
    · exact add_mem_subsetSums_add (replicate_sum_mem p j (t - 1) (by omega))
        (replicate_sum_mem q k Z hkZ)
    · exact Nat.add_le_add (Nat.mul_le_mul_right p (by omega)) (Nat.mul_le_mul_right q hkZ)
    · have heq2 : j * p + a * p = t * k * p + n * p := by
        calc j * p + a * p = (j + a) * p := by ring
        _ = (t * k + n) * p := by rw [hjeq]
        _ = t * k * p + n * p := by ring
      have hjle : j * p ≤ t * k * p + n * p := by omega
      have step_a : Nat.ModEq a (j * p) (t * k * p + n * p) := by
        rw [Nat.modEq_iff_dvd' hjle]
        have hsub : t * k * p + n * p - j * p = a * p := by omega
        rw [hsub]; exact dvd_mul_right a p
      have hkq0 : Nat.ModEq a (k * (q + t * p)) 0 := hqtp.mul_left k
      have step_b : Nat.ModEq a (j * p + k * q) (t * k * p + n * p + k * q) :=
        step_a.add_right (k * q)
      have hre : t * k * p + n * p + k * q = n * p + k * (q + t * p) := by ring
      rw [hre] at step_b
      have step_c : Nat.ModEq a (n * p + k * (q + t * p)) (n * p + 0) := hkq0.add_left (n * p)
      rw [add_zero] at step_c
      have step_d : Nat.ModEq a (j * p + k * q) (n * p) := step_b.trans step_c
      have hfin : Nat.ModEq a (j * p + k * q) c := step_d.trans hn
      have hc' : c % a = c := Nat.mod_eq_of_lt hc
      show (j * p + k * q) % a = c
      rw [← hc']; exact hfin

/-- `residue_frame_neg` packaged with the parent's `centered_frame`. -/
theorem residue_frame_neg_run {a p q t Z M x : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hcop : Nat.Coprime p a) (ht2 : 2 ≤ t)
    (hZ : Z = (a - 1) / t) (hqtp : Nat.ModEq a (q + t * p) 0)
    (hbudget : M - 1 + ((t - 1) * p + Z * q) ≤ a * x) :
    HasRun (subsetSums (Multiset.replicate (t - 1) p + Multiset.replicate Z q +
      Multiset.replicate x a)) M :=
  centered_frame ha
    (fun c hc => (residue_frame_neg ha hp hcop ht2 hZ hqtp c hc).imp
      fun v ⟨hv, hvS, hvc⟩ => ⟨hv, Nat.zero_le v, hvS, hvc⟩)
    (by omega)

end Erdos1112.Proof.Short
