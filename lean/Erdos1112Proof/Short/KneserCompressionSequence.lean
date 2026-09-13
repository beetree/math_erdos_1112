/- Transport the fair sequence and its elementary structure through compression. -/
import Erdos1112Proof.Short.KneserCompression
import Erdos1112Proof.Short.DensityLimit
import Erdos1112Proof.Short.DensityIteration

namespace Erdos1112.Proof.Short.KneserCompression
open Erdos1112.Proof.Short.KneserDensity
open scoped Pointwise

theorem compressedSet_mono {g h : ℕ} {r : Fin h → ℕ} {A A' : Set ℕ}
    (hAA : A ⊆ A') : compressedSet g h r A ⊆ compressedSet g h r A' := by
  rintro n ⟨j,t,ht,rfl⟩
  exact ⟨j,t,hAA ht,rfl⟩

theorem compressedSetZero_mono {g h : ℕ} {B B' : Set ℕ}
    (hBB : B ⊆ B') : compressedSetZero g h B ⊆ compressedSetZero g h B' := by
  rintro n ⟨t,ht,rfl⟩
  exact ⟨t,hBB ht,rfl⟩

theorem compressed_fair {A B : ℕ → Set ℕ} {g h : ℕ} {r : Fin h → ℕ}
    (hfair : FairAbsorption A B) :
    FairAbsorption (fun n => compressedSet g h r (A n))
      (fun n => compressedSetZero g h (B n)) := by
  rintro i a ⟨j,t,ht,rfl⟩
  obtain ⟨l,hli,hl⟩ := hfair i (r j + g*t) ht
  refine ⟨l,hli,?_⟩
  rintro b ⟨s,hs,rfl⟩
  refine ⟨j,t+s,?_,?_⟩
  · convert hl (g*s) hs using 1 <;> ring
  · simp

theorem compressed_initial_interval {A : Set ℕ} {g h : ℕ} {r : Fin h → ℕ}
    (hr : ∀ j, r j ∈ A) : ∀ j < h, j ∈ compressedSet g h r A := by
  intro j hj
  exact ⟨⟨j,hj⟩,0,by simpa using hr ⟨j,hj⟩,by simp [encode]⟩

theorem compressedZero_infinite {B : Set ℕ} {g h : ℕ} (hh : 0 < h)
    (hB : B.Infinite) (hdiv : ∀ b ∈ B, ∃ t, b=g*t) :
    (compressedSetZero g h B).Infinite := by
  let T : Set ℕ := {t | g*t ∈ B}
  have hT : T.Infinite := by
    intro hf
    apply hB
    have heq : B=(fun t => g*t) '' T := by
      ext b
      constructor
      · intro hb
        obtain ⟨t,rfl⟩ := hdiv b hb
        exact ⟨t,hb,rfl⟩
      · rintro ⟨t,ht,rfl⟩; exact ht
    rw [heq]
    exact hf.image _
  have heq : compressedSetZero g h B=(fun t => h*t) '' T := by
    ext n
    constructor
    · rintro ⟨t,ht,rfl⟩; exact ⟨t,ht,rfl⟩
    · rintro ⟨t,ht,rfl⟩; exact ⟨t,ht,rfl⟩
  rw [heq]
  exact hT.image (fun _ _ _ _ heq => Nat.eq_of_mul_eq_mul_left hh heq)

/-- A pair at a divisible distance remains a pair at the compressed distance. -/
theorem compressed_pair {B : Set ℕ} {g h f : ℕ} (hg : 0 < g)
    (hfg : g ∣ f) (hB : ∀ b ∈ B, ∃ t, b=g*t)
    (hpair : ∃ b ∈ B, b+f ∈ B) :
    ∃ b ∈ compressedSetZero g h B, b+h*(f/g) ∈ compressedSetZero g h B := by
  obtain ⟨b,hb,hbf⟩ := hpair
  obtain ⟨t,rfl⟩ := hB b hb
  refine ⟨h*t,⟨t,hb,rfl⟩,t+f/g,?_,?_⟩
  · simpa [mul_add, Nat.mul_div_cancel' hfg] using hbf
  · ring

/-- A cofinite compressed set yields one progression in the original set. -/
theorem hasAPTail_of_compressed_cofinite {S : Set ℕ} {g h : ℕ} {r : Fin h → ℕ}
    (hg : 0 < g) (hh : 0 < h)
    (hc : ∃ N, ∀ n ≥ N, n ∈ compressedSet g h r S) : HasAPTail S := by
  obtain ⟨N,hN⟩ := hc
  refine ⟨g,hg,r ⟨0,hh⟩ + g*N,?_⟩
  intro t
  have hn : N ≤ h*(N+t) := by nlinarith
  obtain ⟨j,s,hs,heq⟩ := hN (h*(N+t)) hn
  have henc : encode h j s = encode h ⟨0,hh⟩ (N+t) := by
    simpa [encode] using heq.symm
  have he := @encode_injective h hh (j,s) (⟨0,hh⟩,N+t) henc
  have hj : j=⟨0,hh⟩ := congrArg Prod.fst he
  have ht : s=N+t := congrArg Prod.snd he
  subst j; subst s
  convert hs using 1 <;> ring

end Erdos1112.Proof.Short.KneserCompression
