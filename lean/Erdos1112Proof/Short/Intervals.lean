/- Short paper Appendix A: elementary interval constructions.
No imports of the old SHARP case analysis, tables, or staircase. -/
import Erdos1112Proof.SubsetSums

namespace Erdos1112.Proof.Short

lemma residue_representative {p q : ℕ} (hq : 0 < q) (hco : Nat.Coprime p q)
    (n : ℕ) : ∃ i, i < q ∧ (i*p)%q = n%q := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).mpr hco
  let x : ZMod q := (n : ZMod q)*hu.unit⁻¹
  refine ⟨x.val,ZMod.val_lt _,?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]
  change ((n : ZMod q)*↑hu.unit⁻¹)*(p : ZMod q) = n
  rw [mul_assoc,hu.val_inv_mul,mul_one]

lemma replicate_sum_mem (p i x : ℕ) (hi : i ≤ x) :
    i*p ∈ subsetSums (Multiset.replicate x p) := by
  apply mem_subsetSums.mpr
  refine ⟨Multiset.replicate i p,(Multiset.replicate_le_replicate p).mpr hi,?_⟩
  simp

/-- The short paper's coprime rectangle, proved directly by a residue choice. -/
theorem coprime_rectangle {p q : ℕ} (hp : 0 < p) (hpq : p < q)
    (hco : Nat.Coprime p q) :
    HasRun (subsetSums (Multiset.replicate (q-1) p +
      Multiset.replicate (p-1) q)) (p+q-1) := by
  have hq : 0 < q := by omega
  refine ⟨(p-1)*(q-1),fun t ht => ?_⟩
  let n := (p-1)*(q-1)+t
  obtain ⟨i,hi,hres⟩ := residue_representative hq hco n
  let j : ℤ := ((n : ℤ)-(i : ℤ)*p)/q
  have hmod : (i*p : ℕ) ≡ n [MOD q] := hres
  have hdvd : (q : ℤ) ∣ (n : ℤ)-(i : ℤ)*p := by
    have := (Int.natCast_modEq_iff).mpr hmod
    exact Int.modEq_iff_dvd.mp this
  have hj : j*(q : ℤ) = (n : ℤ)-(i : ℤ)*p := Int.ediv_mul_cancel hdvd
  have hnlo : ((p-1)*(q-1) : ℕ) ≤ n := Nat.le_add_right _ _
  have hnhi : n ≤ p*q-1 := by
    dsimp [n]
    have he : (p-1)*(q-1)+p+q = p*q+1 := by
      zify [show 1 ≤ p from hp,show 1 ≤ q from hq]; ring
    omega
  have hc : (((p-1)*(q-1) : ℕ) : ℤ) = ((p : ℤ)-1)*(q-1) := by
    push_cast [Nat.cast_sub hp,Nat.cast_sub hq]; rfl
  have hlo : ((p : ℤ)-1)*(q-1) ≤ n := by exact_mod_cast (hc ▸ (show (((p-1)*(q-1) : ℕ) : ℤ) ≤ n by exact_mod_cast hnlo))
  have hhi : (n : ℤ) ≤ (p : ℤ)*q-1 := by
    have hpos : 0 < p*q := Nat.mul_pos hp hq
    have hn : n+1 ≤ p*q := by omega
    have hz : (n : ℤ)+1 ≤ (p : ℤ)*q := by exact_mod_cast hn
    omega
  have hj0 : 0 ≤ j := by
    have hiZ : (i : ℤ) ≤ (q : ℤ)-1 := by omega
    have := mul_le_mul_of_nonneg_right hiZ (show (0 : ℤ) ≤ p by positivity)
    nlinarith
  have hjp : j < p := by nlinarith
  have hrep : n = i*p+j.toNat*q := by
    have hjcast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
    have he : (n : ℤ) = (i : ℤ)*p+(j.toNat : ℤ)*q := by rw [hjcast]; omega
    exact_mod_cast he
  change n ∈ _
  rw [hrep]
  exact add_mem_subsetSums_add (replicate_sum_mem p i (q-1) (by omega))
    (replicate_sum_mem q j.toNat (p-1) (by omega))

lemma subsetSums_scale (d : ℕ) (C : Multiset ℕ) :
    subsetSums (C.map (d*·)) = (subsetSums C).image (d*·) := by
  induction C using Multiset.induction with
  | empty => simp
  | cons x C ih =>
    rw [Multiset.map_cons,subsetSums_cons,subsetSums_cons,ih,
      Finset.image_union,Finset.image_image,Finset.image_image]
    congr 1
    have he : ((d*·) ∘ (x+·)) = ((d*x+·) ∘ (d*·)) := by funext n; simp; ring
    rw [he]

/-- Interlacing scaled intervals. A fixed natural starting point avoids
negative representative indices: start at d*A+(d-1)*q. -/
theorem interlacing {d q N : ℕ} {C : Multiset ℕ}
    (hd : 0 < d) (hco : Nat.Coprime d q) (hqN : q ≤ N)
    (hrun : HasRun (subsetSums C) N) :
    HasRun (subsetSums (C.map (d*·)+Multiset.replicate (d-1) q)) N := by
  obtain ⟨A,hA⟩ := hrun
  refine ⟨d*A+(d-1)*q,fun n hn => ?_⟩
  let X := (d-1)*q+n
  obtain ⟨j,hj,hres⟩ := residue_representative hd hco.symm X
  have hjq : j*q ≤ X := by
    have := Nat.mul_le_mul_right q (show j ≤ d-1 by omega)
    dsimp [X]; omega
  have hdvd : d ∣ X-j*q := (Nat.modEq_iff_dvd' hjq).mp hres
  let t := (X-j*q)/d
  have ht : t*d = X-j*q := Nat.div_mul_cancel hdvd
  have hXN : X < d*N := by
    have := Nat.mul_le_mul_left (d-1) hqN
    have he : (d-1)*N+N = d*N := by
      have hd1 : d-1+1 = d := by omega
      nlinarith [hd1]
    dsimp [X]; omega
  have htN : t < N := by
    exact Nat.lt_of_mul_lt_mul_right (show t*d < N*d by
      have : t*d ≤ X := by omega
      nlinarith)
  have hs : d*(A+t) ∈ subsetSums (C.map (d*·)) := by
    rw [subsetSums_scale]
    exact Finset.mem_image_of_mem _ (hA t htN)
  have hjmem := replicate_sum_mem q j (d-1) (by omega)
  have heq : d*A+(d-1)*q+n = d*(A+t)+j*q := by
    dsimp [X] at ht hjq
    have he : t*d+j*q = (d-1)*q+n := by omega
    nlinarith [he]
  rw [heq]
  exact add_mem_subsetSums_add hs hjmem

/-- Centered frame: the padding pays for U-L, not U. -/
theorem centered_frame {a x L U M : ℕ} {C : Multiset ℕ} (ha : 0 < a)
    (hreps : ∀ r < a, ∃ v ∈ subsetSums C, L ≤ v ∧ v ≤ U ∧ v%a = r)
    (hbudget : M-1+U ≤ L+a*x) :
    HasRun (subsetSums (C+Multiset.replicate x a)) M := by
  refine ⟨U,fun i hi => ?_⟩
  let n := U+i
  obtain ⟨v,hv,hLv,hvU,hmod⟩ := hreps (n%a) (Nat.mod_lt _ ha)
  have hvn : v ≤ n := by dsimp [n]; omega
  have hdvd : a ∣ n-v := (Nat.modEq_iff_dvd' hvn).mp hmod
  let t := (n-v)/a
  have ht : t*a = n-v := Nat.div_mul_cancel hdvd
  have htx : t ≤ x := by
    have hp : t*a ≤ x*a := by
      dsimp [n] at ht hvn
      have he : t*a+v = U+i := by omega
      have hile : i ≤ M-1 := by omega
      nlinarith [he]
    exact Nat.le_of_mul_le_mul_right hp ha
  have heq : U+i = v+t*a := by dsimp [n] at ht hvn; omega
  rw [heq]
  exact add_mem_subsetSums_add hv (replicate_sum_mem a t x htx)

/-- Adjoining repeated copies extends an interval by overlapping translates. -/
lemma extend_run {S : Multiset ℕ} {ℓ a : ℕ} (ha : a ≤ ℓ)
    (h : HasRun (subsetSums S) ℓ) (t : ℕ) :
    HasRun (subsetSums (Multiset.replicate t a+S)) (ℓ+t*a) := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    have h2 : a ≤ ℓ+t*a := by omega
    have h3 := HasRun.cons_of_le h2 ih
    have e1 : a ::ₘ (Multiset.replicate t a+S) =
        Multiset.replicate (t+1) a+S := by
      rw [Multiset.replicate_succ,Multiset.cons_add]
    have e2 : ℓ+t*a+a = ℓ+(t+1)*a := by ring
    rwa [e1,e2] at h3

/-- The paper's two-generator target lemma, with the stated floor saving. -/
theorem two_generator_target {p h N : ℕ} (hp : 0 < p) (hph : p < h)
    (hco : Nat.Coprime p h) (hN : 2*h ≤ N) :
    ∃ S : Multiset ℕ, (∀ v ∈ S, v = p ∨ v = h) ∧
      S.card ≤ N-N/h ∧ HasRun (subsetSums S) N := by
  let s := N/h
  let r := N%h
  have hh : 0 < h := by omega
  have hs : 2 ≤ s := (Nat.le_div_iff_mul_le hh).mpr hN
  have hr : r < h := Nat.mod_lt _ hh
  have hdecomp : N = s*h+r := by simpa [s,r,Nat.mul_comm] using (Nat.div_add_mod N h).symm
  let t := s-1+if r ≥ p then 1 else 0
  let C := Multiset.replicate (h-1) p+Multiset.replicate (p-1) h
  let S := Multiset.replicate t h+C
  have hrun := extend_run (show h ≤ p+h-1 by omega)
    (coprime_rectangle hp hph hco) t
  have hlen : N ≤ p+h-1+t*h := by
    dsimp [t]
    split_ifs with hcase
    · have he : s-1+1 = s := by omega
      rw [he]
      omega
    · have he : (s-1)*h+h = s*h := by
        have : s-1+1=s := by omega
        nlinarith
      simp only [Nat.add_zero]
      omega
  refine ⟨S, ?_, ?_, HasRun.of_le hlen hrun⟩
  · intro v hv
    change v ∈ Multiset.replicate t h+C at hv
    rcases Multiset.mem_add.mp hv with hv | hv
    · exact Or.inr (Multiset.mem_replicate.mp hv).2
    · rcases Multiset.mem_add.mp hv with hv | hv
      · exact Or.inl (Multiset.mem_replicate.mp hv).2
      · exact Or.inr (Multiset.mem_replicate.mp hv).2
  · have hcard : S.card = t+(h-1)+(p-1) := by simp [S,C]; omega
    rw [hcard]
    have hh2 : 2 ≤ h := by omega
    have hs2 : s-2+2=s := by omega
    have hh2' : h-2+2=h := by omega
    have hbound : 2*s+2*h ≤ s*h+4 := by
      nlinarith [Nat.zero_le ((s-2)*(h-2))]
    have hp1 : p-1+1=p := by omega
    have hh1 : h-1+1=h := by omega
    have hsN : s ≤ N := by nlinarith
    have hNs : N-s+s=N := by omega
    dsimp [t]
    split_ifs with hcase
    · have he : s-1+1=s := by omega
      rw [he]
      change _ ≤ N-s
      omega
    · change _ ≤ N-s
      omega

end Erdos1112.Proof.Short
