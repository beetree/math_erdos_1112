/- Reciprocal Beatty interpolation, short paper §1. -/
import Erdos1112Proof.Existence.Beatty

namespace Erdos1112.Proof

lemma fractional_component {q u v lo hi : ℝ} (hq : 0 < q)
    (hu : 0 < u) (_huv : u < v) (hv : v < 1)
    (hwidth : 1 + (v - u) ≤ q * (hi - lo)) :
    ∃ lo' hi' : ℝ, lo ≤ lo' ∧ hi' ≤ hi ∧
      hi' - lo' = (v - u) / q ∧
      ∀ θ ∈ Set.Icc lo' hi', Int.fract (q * θ) ∈ Set.Icc u v := by
  let m : ℤ := ⌈q * lo - u⌉
  have hmlo : q * lo - u ≤ (m : ℝ) := Int.le_ceil _
  have hmhi : (m : ℝ) < q * lo - u + 1 := Int.ceil_lt_add_one _
  refine ⟨(m + u) / q, (m + v) / q, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hq).mpr; nlinarith
  · apply (div_le_iff₀ hq).mpr; nlinarith
  · ring
  · intro θ hθ
    have hl := (div_le_iff₀ hq).mp hθ.1
    have hh := (le_div_iff₀ hq).mp hθ.2
    have hf : ⌊q * θ⌋ = m := by
      apply Int.floor_eq_iff.mpr
      constructor <;> nlinarith
    rw [← Int.self_sub_floor, hf]
    constructor <;> nlinarith

set_option maxHeartbeats 800000 in
/-- Nested fractional-part components, with division-free growth hypothesis. -/
theorem reciprocal_interpolation (b : ℕ → ℕ) (hb : StrictMono b)
    (hb0 : 0 < b 0) {u v lo hi : ℝ}
    (hu : 0 < u) (huv : u < v) (hv : v < 1) (hlohi : lo < hi)
    (hscale : ∀ i, (1 + (v-u)) * (b i : ℝ) ≤ (v-u) * b (i+1)) :
    ∃ θ ∈ Set.Icc lo hi, ∃ N : ℕ, ∀ i, N ≤ i →
      Int.fract ((b i : ℝ) * θ) ∈ Set.Icc u v := by
  classical
  have hell : 0 < v-u := sub_pos.mpr huv
  have hbpos : ∀ i, (0 : ℝ) < b i := by
    intro i
    have := hb.monotone (Nat.zero_le i)
    exact_mod_cast (show 0 < b i by omega)
  obtain ⟨N, hN⟩ := exists_nat_ge ((1 + (v-u)) / (hi-lo))
  have hNb : (N : ℝ) ≤ (b N : ℝ) := by exact_mod_cast hb.le_apply (x := N)
  have hstart : 1 + (v-u) ≤ (b N : ℝ) * (hi-lo) := by
    have := (div_le_iff₀ (sub_pos.mpr hlohi)).mp hN
    nlinarith
  let Q : ℕ → ℝ × ℝ → ℝ × ℝ → Prop := fun j p p' =>
    p.1 ≤ p'.1 ∧ p'.2 ≤ p.2 ∧ p'.2-p'.1 = (v-u)/(b (N+j) : ℝ) ∧
      ∀ θ ∈ Set.Icc p'.1 p'.2,
        Int.fract ((b (N+j) : ℝ)*θ) ∈ Set.Icc u v
  let next : ℕ → ℝ × ℝ → ℝ × ℝ := fun j p =>
    if h : ∃ p', Q j p p' then h.choose else p
  let chain : ℕ → ℝ × ℝ := fun j => Nat.rec (lo, hi) next j
  have hc0 : chain 0 = (lo, hi) := rfl
  have hcs : ∀ j, chain (j+1) = next j (chain j) := fun _ => rfl
  have main : ∀ j, lo ≤ (chain j).1 ∧ (chain j).2 ≤ hi ∧
      1+(v-u) ≤ (b (N+j) : ℝ)*((chain j).2-(chain j).1) := by
    intro j
    induction j with
    | zero => simpa [chain] using And.intro (le_refl lo) (And.intro (le_refl hi) hstart)
    | succ j ih =>
      obtain ⟨l, h, hl, hh, hw, hs⟩ :=
        fractional_component (hbpos (N+j)) hu huv hv ih.2.2
      have hE : ∃ p', Q j (chain j) p' := ⟨(l,h), hl, hh, hw, hs⟩
      have hnext : chain (j+1) = hE.choose := by
        rw [hcs]; exact dif_pos hE
      have hQ := hE.choose_spec
      change (chain j).1 ≤ hE.choose.1 ∧ hE.choose.2 ≤ (chain j).2 ∧
        hE.choose.2-hE.choose.1 = (v-u)/(b (N+j) : ℝ) ∧ _ at hQ
      rw [hnext]
      refine ⟨ih.1.trans hQ.1, hQ.2.1.trans ih.2.1, ?_⟩
      rw [hQ.2.2.1]
      have hg := hscale (N+j)
      rw [show N+j+1 = N+(j+1) from by omega] at hg
      rw [← mul_div_assoc, le_div_iff₀ (hbpos (N+j))]
      nlinarith
  have hstep : ∀ j, Q j (chain j) (chain (j+1)) := by
    intro j
    obtain ⟨l,h,hl,hh,hw,hs⟩ :=
      fractional_component (hbpos (N+j)) hu huv hv (main j).2.2
    have hE : ∃ p', Q j (chain j) p' := ⟨(l,h),hl,hh,hw,hs⟩
    have heq : chain (j+1) = hE.choose := by rw [hcs]; exact dif_pos hE
    rw [heq]; exact hE.choose_spec
  have hvalid : ∀ j, (chain j).1 ≤ (chain j).2 := by
    intro j
    have := (main j).2.2
    have := hbpos (N+j)
    nlinarith
  have hmono : Monotone fun j => (chain j).1 :=
    monotone_nat_of_le_succ fun j => (hstep j).1
  have hanti : Antitone fun j => (chain j).2 :=
    antitone_nat_of_succ_le fun j => (hstep j).2.1
  have hbdd : BddAbove (Set.range fun j => (chain j).1) :=
    ⟨hi, by rintro x ⟨j,rfl⟩; exact (hvalid j).trans (main j).2.1⟩
  let θ : ℝ := ⨆ j, (chain j).1
  have hθlo : ∀ j, (chain j).1 ≤ θ := fun j => le_ciSup hbdd j
  have hθhi : ∀ j, θ ≤ (chain j).2 := by
    intro j
    apply ciSup_le
    intro m
    rcases le_total m j with hm | hm
    · exact (hmono hm).trans (hvalid j)
    · exact (hvalid m).trans (hanti hm)
  refine ⟨θ, ⟨?_, ?_⟩, N, ?_⟩
  · simpa [hc0] using hθlo 0
  · simpa [hc0] using hθhi 0
  · intro i hiN
    have hs := (hstep (i-N)).2.2.2 θ ⟨hθlo (i-N+1),hθhi (i-N+1)⟩
    simpa [Nat.add_sub_of_le hiN] using hs

set_option maxHeartbeats 1000000 in
/-- The short paper's improved bound, proved by reciprocal interpolation. -/
theorem existence_bound_reciprocal (k d₁ d₂ : ℕ) (hk : 3 ≤ k)
    (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) (h : k+1 ≤ d₂) :
    RatioWorks k d₁ d₂ (d₂+2) := by
  classical
  intro b hb
  let D : ℝ := d₂
  have hD : (4 : ℝ) ≤ D := by dsimp [D]; exact_mod_cast (show 4 ≤ d₂ by omega)
  have hD0 : 0 < D := by linarith
  have hDm : 0 < D-1 := by linarith
  have hDp : 0 < D+1 := by linarith
  let ε : ℝ := 1/(2*D*(D+1))
  let u : ℝ := ε
  let v : ℝ := ε+1/(D+1)
  let lo : ℝ := 1/D
  let hi : ℝ := 1/D+ε/(D-1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεlt : ε < 1/D := by
    dsimp [ε]
    apply (div_lt_div_iff₀ (by positivity) hD0).mpr
    nlinarith
  have hvEq : v = 1/D-ε := by
    dsimp [v, ε]
    field_simp
    ring
  have huv : u < v := by
    dsimp [u,v]
    linarith [one_div_pos.mpr hDp]
  have hv1 : v < 1 := by
    rw [hvEq]
    have hiD : 1/D < 1 := (div_lt_one hD0).mpr (by linarith)
    linarith
  have hlohi : lo < hi := by
    dsimp [lo,hi]
    have : 0 < ε/(D-1) := div_pos hε hDm
    linarith
  have hscale : ∀ i, (1+(v-u))*(b i : ℝ) ≤ (v-u)*b (i+1) := by
    intro i
    have hr : (D+2)*(b i : ℝ) ≤ b (i+1) := by
      dsimp [D]; exact_mod_cast hb.2.2 i
    have hlen : v-u = 1/(D+1) := by dsimp [v,u]; ring
    rw [hlen]
    have he : 1+1/(D+1) = (D+2)/(D+1) := by field_simp; ring
    rw [he, div_mul_eq_mul_div, one_div_mul_eq_div]
    exact (div_le_div_iff_of_pos_right hDp).mpr hr
  obtain ⟨θ,hθ,N,hN⟩ := reciprocal_interpolation b hb.2.1 hb.1 hε huv hv1 hlohi hscale
  have hθlo : 1/D ≤ θ := hθ.1
  have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθlo
  have hhi : (D-1)*hi = 1-1/D+ε := by
    dsimp [hi]
    field_simp
  have hθhi : (D-1)*θ ≤ 1-1/D+ε := by
    calc (D-1)*θ ≤ (D-1)*hi := mul_le_mul_of_nonneg_left hθ.2 hDm.le
      _ = _ := hhi
  have hroom : v+(k : ℝ)*θ ≤ 1 := by
    have hkD : (k : ℝ) ≤ D-1 := by dsimp [D]; exact_mod_cast (show (k : ℤ) ≤ (d₂ : ℤ)-1 by omega)
    have := mul_le_mul_of_nonneg_right hkD hθ0.le
    rw [hvEq]
    linarith
  let α : ℝ := 1/θ
  have hαθ : α*θ = 1 := div_mul_cancel₀ 1 (ne_of_gt hθ0)
  have hαl : D-1 < α := by
    apply (mul_lt_mul_iff_left₀ hθ0).mp
    rw [hαθ]
    nlinarith
  have hαu : α ≤ D := by
    apply (mul_le_mul_iff_left₀ hθ0).mp
    rw [hαθ]
    have := (div_le_iff₀ hD0).mp hθlo
    nlinarith
  have hα0 : 0 < α := by dsimp [α]; positivity
  have hg : HasGapsIn d₁ d₂ (beatty α 0) := beatty_hasGapsIn hd₁ hd hαl hαu
  let m : ℕ := b N+1
  let a : ℕ → ℕ := fun i => beatty α 0 (m+i)
  have ha : HasGapsIn d₁ d₂ a := by
    refine ⟨?_,fun i => ?_⟩
    · have := hg.strictMono hd₁ |>.monotone (Nat.zero_le m)
      have := hg.1
      dsimp [a]; omega
    · simpa [a, Nat.add_assoc] using hg.2 (m+i)
  refine ⟨a,ha,disjoint_range_iff.mpr ?_⟩
  intro x hx i heq
  subst x
  by_cases hiN : i < N
  · obtain ⟨f,hf⟩ := hx
    have hbi : b i ≤ b N := hb.2.1.monotone (by omega)
    have hm : m ≤ beatty α 0 m := (hg.strictMono hd₁).le_apply
    have hsum : k*a 0 ≤ ∑ j, a (f j) := by
      calc k*a 0 = ∑ _j : Fin k, a 0 := by simp [Finset.sum_const]
        _ ≤ ∑ j, a (f j) := Finset.sum_le_sum fun j _ =>
          ha.monotone (Nat.zero_le _)
    have ham : m ≤ a 0 := by simpa [a] using hm
    have hka : a 0 ≤ k*a 0 := Nat.le_mul_of_pos_left _ (by omega)
    dsimp [m] at ham
    omega
  · have hbmem : b i ∈ kFoldSumset k (beatty α 0) := by
      obtain ⟨f,hf⟩ := hx
      exact ⟨fun j => m+f j,hf⟩
    obtain ⟨s,hs,hbelow,habove⟩ := beatty_mem_cluster (by omega : 0 < k) hα0 hbmem
    simp only [Nat.cast_zero, mul_zero, zero_add] at hbelow habove
    have hlow := mul_le_mul_of_nonneg_right habove hθ0.le
    have hupp := mul_lt_mul_of_pos_right hbelow hθ0
    have hsθ : (s : ℝ)*α*θ = s := by rw [mul_assoc,hαθ,mul_one]
    have hbl : (b i : ℝ)*θ ≤ s := by nlinarith [hsθ]
    have hbu : (s : ℝ) < (b i : ℝ)*θ+(k : ℝ)*θ := by nlinarith [hsθ]
    have hsafe := hN i (by omega)
    have hfpos : 0 < Int.fract ((b i : ℝ)*θ) := lt_of_lt_of_le hε hsafe.1
    have hftop : Int.fract ((b i : ℝ)*θ)+(k : ℝ)*θ ≤ 1 := by linarith [hsafe.2]
    rw [← Int.self_sub_floor] at hfpos hftop
    have hfloor : (⌊(b i : ℝ)*θ⌋ : ℝ) < s := by linarith
    have hfloorZ : ⌊(b i : ℝ)*θ⌋+1 ≤ (s : ℤ) := by
      have : ⌊(b i : ℝ)*θ⌋ < (s : ℤ) := by exact_mod_cast hfloor
      omega
    have hfloorR : (⌊(b i : ℝ)*θ⌋ : ℝ)+1 ≤ s := by exact_mod_cast hfloorZ
    linarith

end Erdos1112.Proof
