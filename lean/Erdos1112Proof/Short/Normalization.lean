/- The short paper's initial translation and gcd normalization of a walk. -/
import Erdos1112Proof.Short.GapWord

namespace Erdos1112.Proof.Short

/-- Dividing a finite alphabet by its gcd preserves its cardinality, normalizes
its gcd, and keeps exactly the rescaled letters. -/
lemma gcd_image_div {G : Finset ℕ} {g : ℕ} (hdiv : ∀ x ∈ G, g ∣ x) :
    (G.image (·/g)).gcd id*g=G.gcd id := by
  induction G using Finset.induction with
  | empty => simp
  | insert x G hx ih =>
    rw [Finset.image_insert,Finset.gcd_insert,Finset.gcd_insert]
    have hxg := hdiv x (Finset.mem_insert_self _ _)
    have ih' := ih (fun y hy => hdiv y (Finset.mem_insert_of_mem hy))
    simp only [id_eq]
    rw [← ih']
    change Nat.gcd (x/g) ((G.image (·/g)).gcd id)*g =
      Nat.gcd x ((G.image (·/g)).gcd id*g)
    rw [← Nat.gcd_mul_right,Nat.div_mul_cancel hxg]

/-- The divided alphabet has gcd one and the same number of letters. -/
lemma normalized_alphabet {G : Finset ℕ} (hne : G.Nonempty)
    (hpos : ∀ x ∈ G, 0 < x) :
    let g := G.gcd id
    0 < g ∧ (G.image (·/g)).gcd id=1 ∧
      (G.image (·/g)).card=G.card ∧
      (∀ x ∈ G.image (·/g), 0 < x ∧ g*x ∈ G) := by
  dsimp only
  let g := G.gcd id
  have hdvd : ∀ x ∈ G, g ∣ x := fun x hx => Finset.gcd_dvd hx
  have hg : 0 < g := by
    obtain ⟨x,hx⟩ := hne
    have hxp := hpos x hx
    by_contra hn
    have hg0 : g=0 := by omega
    have := hdvd x hx
    rw [hg0,zero_dvd_iff] at this
    omega
  have hgcd : (G.image (·/g)).gcd id=1 := by
    have he := gcd_image_div hdvd
    change (G.image (·/g)).gcd id*g=g at he
    exact Nat.eq_of_mul_eq_mul_right hg (he.trans (Nat.one_mul g).symm)
  have hinj : Set.InjOn (·/g) G := by
    intro x hx y hy he
    have h1 := Nat.div_mul_cancel (hdvd x hx)
    have h2 := Nat.div_mul_cancel (hdvd y hy)
    change x/g=y/g at he
    rw [he] at h1
    omega
  refine ⟨hg,hgcd,Finset.card_image_of_injOn hinj,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  refine ⟨Nat.div_pos (Nat.le_of_dvd (hpos y hy) (hdvd y hy)) hg,?_⟩
  rwa [Nat.mul_div_cancel' (hdvd y hy)]

/-- A tail is a translate of a positive integer multiple of a walk starting at
zero, with exactly the divided gaps. -/
theorem normalize_tail {a : ℕ → ℕ} {g T : ℕ}
    (hmono : StrictMono a) (hg : 0 < g)
    (hdiv : ∀ n, g ∣ a (T+n+1)-a (T+n)) :
    ∃ P : ℕ → ℕ, P 0=0 ∧ StrictMono P ∧
      (∀ n, a (T+n)=a T+g*P n) ∧
      (∀ n, P (n+1)-P n=(a (T+n+1)-a (T+n))/g) := by
  have hdivprefix : ∀ n, g ∣ a (T+n)-a T := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hdiv n
      have h1 := hmono.monotone (show T ≤ T+n by omega)
      have h2 := hmono.monotone (show T+n ≤ T+n+1 by omega)
      have he : a (T+(n+1))-a T =
          (a (T+n+1)-a (T+n))+(a (T+n)-a T) := by
        rw [show T+(n+1)=T+n+1 by omega]
        omega
      rw [he]
      exact dvd_add hh ih
  let P := fun n => (a (T+n)-a T)/g
  have hmul : ∀ n, g*P n=a (T+n)-a T := fun n =>
    Nat.mul_div_cancel' (hdivprefix n)
  have haff : ∀ n, a (T+n)=a T+g*P n := by
    intro n
    rw [hmul]
    have := hmono.monotone (show T ≤ T+n by omega)
    omega
  have hPmono : StrictMono P := by
    intro i j hij
    have hh := hmono (show T+i < T+j by omega)
    rw [haff i,haff j] at hh
    exact Nat.lt_of_mul_lt_mul_left (show g*P i < g*P j by omega)
  refine ⟨P,by simp [P],hPmono,haff,fun n => ?_⟩
  have he : g*(P (n+1)-P n)=a (T+n+1)-a (T+n) := by
    have hP := hPmono.monotone (show n ≤ n+1 by omega)
    rw [Nat.mul_sub,Nat.add_assoc,haff (n+1),haff n]
    omega
  have hh : (g*(P (n+1)-P n))/g=P (n+1)-P n :=
    Nat.mul_div_cancel_left _ hg
  rw [he] at hh
  exact hh.symm

/-- Every admissible walk has a normalized tail whose finite alphabet consists
exactly of its recurring gaps and has gcd one. -/
theorem normalized_walk {a : ℕ → ℕ} {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁)
    (hgaps : HasGapsIn d₁ d₂ a) :
    ∃ (T g : ℕ) (P : ℕ → ℕ) (H : Finset ℕ),
      0 < g ∧ P 0=0 ∧ StrictMono P ∧
      (∀ n, a (T+n)=a T+g*P n) ∧ H.Nonempty ∧
      (∀ x ∈ H, 0 < x ∧ x ≤ d₂) ∧ H.gcd id=1 ∧
      (∀ n, gap P n ∈ H) ∧
      (∀ x ∈ H, ∀ N, ∃ n ≥ N, gap P n=x) := by
  classical
  obtain ⟨T,hT⟩ := exists_tail_index hgaps
  let G := (Finset.Icc d₁ d₂).filter (· ∈ tailAlphabet a)
  have hGiff : ∀ x, x ∈ G ↔ x ∈ tailAlphabet a := by
    intro x
    constructor
    · intro hx; exact (Finset.mem_filter.mp hx).2
    · intro hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (mem_tailAlphabet_bounds hgaps hx),hx⟩
  have hmem : ∀ n, gap a (T+n) ∈ G := by
    intro n
    exact (hGiff _).mpr (hT _ (by omega))
  have hGne : G.Nonempty := ⟨gap a (T+0),hmem 0⟩
  have hGpos : ∀ x ∈ G, 0 < x := by
    intro x hx
    have := (mem_tailAlphabet_bounds hgaps ((hGiff x).mp hx)).1
    omega
  let g := G.gcd id
  have hdvd : ∀ x ∈ G, g ∣ x := fun x hx => Finset.gcd_dvd hx
  obtain ⟨hg,hHgcd,hHcard,hHpos⟩ := normalized_alphabet hGne hGpos
  change 0 < g at hg
  have hdiv : ∀ n, g ∣ a (T+n+1)-a (T+n) := fun n => hdvd _ (hmem n)
  obtain ⟨P,hP0,hPmono,haff,hPgap⟩ := normalize_tail (hgaps.strictMono hd₁) hg hdiv
  let H := G.image (·/g)
  have hHne : H.Nonempty := hGne.image _
  have hgap : ∀ n, gap P n=gap a (T+n)/g := hPgap
  refine ⟨T,g,P,H,hg,hP0,hPmono,haff,hHne,?_,hHgcd,?_,?_⟩
  · intro x hx
    refine ⟨(hHpos x hx).1,?_⟩
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact (Nat.div_le_self y g).trans
      (mem_tailAlphabet_bounds hgaps ((hGiff y).mp hy)).2
  · intro n
    rw [hgap]
    exact Finset.mem_image_of_mem _ (hmem n)
  · intro x hx N
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t,ht,hgt⟩ := (hGiff y).mp hy (T+N)
    refine ⟨t-T,by omega,?_⟩
    rw [hgap,show T+(t-T)=t by omega,hgt]

end Erdos1112.Proof.Short
