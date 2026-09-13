/- Interfaces for assembling the short paper's normalized cases. -/
import Erdos1112Proof.Short.Normalization
import Erdos1112Proof.Short.Slots
import Erdos1112Proof.Short.BinaryGrowth
import Erdos1112Proof.Sharp.Defs

namespace Erdos1112.Proof.Short

/-- Bounded gaps give the linear growth estimate used in the density branch. -/
lemma growth_of_gap_bound {P : ℕ → ℕ} {M : ℕ}
    (hzero : P 0=0) (hmono : StrictMono P) (hgap : ∀ n, gap P n ≤ M) :
    ∀ n, P n ≤ M*n := by
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    have hm := hmono.monotone (show n ≤ n+1 by omega)
    have hs : P (n+1)=P n+gap P n := by dsimp [gap]; omega
    have hg := hgap n
    rw [hs]
    nlinarith

/-- Growth strictly below the summand count, the input to the Kneser shortcut. -/
def SmallGrowth (k : ℕ) (P : ℕ → ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c < k ∧
    ∀ᶠ n in Filter.atTop, (P n : ℝ) ≤ c*n+C

/-- The normalized case split of the paper. Its remaining inputs are
explicit: the density shortcut and SHARP must be proved before this can close
the final theorem. The binary growth/covering alternative is discharged here. -/
theorem normalized_cases {k : ℕ} (hk : 3 ≤ k)
    (hdensity : ∀ P : ℕ → ℕ, P 0=0 → StrictMono P → SmallGrowth k P → TailCovering k P)
    (hsharp : ∀ M, SharpAt M)
    (P : ℕ → ℕ) (G : Finset ℕ) (hP0 : P 0=0) (hmono : StrictMono P)
    (hGne : G.Nonempty) (hGpos : ∀ x ∈ G, 0 < x ∧ x ≤ k)
    (hGgcd : G.gcd id=1) (hGgap : ∀ n, gap P n ∈ G)
    (hrec : ∀ x ∈ G, ∀ N, ∃ n ≥ N, gap P n=x) : TailCovering k P := by
  classical
  let M := G.max' hGne
  have hMG : M ∈ G := Finset.max'_mem _ _
  have hMpos : 0 < M := (hGpos M hMG).1
  have hMk : M ≤ k := (hGpos M hMG).2
  have hmax : ∀ x ∈ G, x ≤ M := fun x hx => Finset.le_max' _ x hx
  have hgM : ∀ n, gap P n ≤ M := fun n => hmax _ (hGgap n)
  by_cases hcrit : M < k
  · apply hdensity P hP0 hmono
    refine ⟨(M : ℝ),0,by exact_mod_cast hMpos,by exact_mod_cast hcrit,?_⟩
    apply Filter.Eventually.of_forall
    intro n
    have hh := growth_of_gap_bound hP0 hmono hgM n
    simpa using (show (P n : ℝ) ≤ (M : ℝ)*n by exact_mod_cast hh)
  have hMk' : M=k := by omega
  have hkG : k ∈ G := hMk' ▸ hMG
  by_cases hcard : 3 ≤ G.card
  · obtain ⟨S,hSmem,hScard,hSrun⟩ := hsharp M G
      (fun x hx => (hGpos x hx).1) hcard hGgcd hmax hMG
    apply TailCovering.of_cofinite
    apply slots_from_run hP0 hmono hMpos ?_ ?_ (hScard.trans (by omega)) (by omega) hSrun
    · intro n
      have hm := hmono.monotone (show n ≤ n+1 by omega)
      have hh := hgM n
      dsimp [gap] at hh
      omega
    · intro δ hδ
      obtain ⟨n,_,hn⟩ := hrec δ (hSmem δ hδ) 0
      refine ⟨n,?_⟩
      have hm := hmono.monotone (show n ≤ n+1 by omega)
      dsimp [gap] at hn
      omega
  have hcard2 : G.card=2 := by
    have hcard0 := hGne.card_pos
    by_contra hn
    have hcard1 : G.card=1 := by omega
    obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hcard1
    have hkx : k=x := by simpa [hx] using hkG
    have hx1 : x=1 := by simpa [hx] using hGgcd
    omega
  obtain ⟨x,y,hxy,hG⟩ := Finset.card_eq_two.mp hcard2
  have hkmem : k=x ∨ k=y := by simpa [hG] using hkG
  obtain ⟨δ,hδne,hshape⟩ : ∃ δ, δ ≠ k ∧ G={δ,k} := by
    rcases hkmem with h | h
    · subst x
      exact ⟨y,Ne.symm hxy,by simpa [Finset.pair_comm] using hG⟩
    · subst y
      exact ⟨x,hxy,hG⟩
  have hδG : δ ∈ G := by simp [hshape]
  have hδpos : 0 < δ := (hGpos δ hδG).1
  have hδk : δ < k := lt_of_le_of_ne (hGpos δ hδG).2 hδne
  have hco : Nat.Coprime δ k := by simpa [hshape] using hGgcd
  have hb := binary_dichotomy hk hP0 hmono hδpos hδk hco
    (fun n => by simpa [hshape] using hGgap n) (hrec δ hδG)
  rcases hb with hgrowth | hcover
  · exact hdensity P hP0 hmono hgrowth
  · exact hcover

/-- Lift the completed normalized case theorem to an arbitrary admissible walk.
The case theorem is an explicit input to this assembly interface. -/
theorem tailCovering_of_normalized_cases {k : ℕ}
    (hcases : ∀ (P : ℕ → ℕ) (G : Finset ℕ), P 0=0 → StrictMono P →
      G.Nonempty → (∀ x ∈ G, 0 < x ∧ x ≤ k) → G.gcd id=1 →
      (∀ n, gap P n ∈ G) →
      (∀ x ∈ G, ∀ N, ∃ n ≥ N, gap P n=x) → TailCovering k P)
    {a : ℕ → ℕ} {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁)
    (hgaps : HasGapsIn d₁ d₂ a) (hd₂ : d₂ ≤ k) : TailCovering k a := by
  obtain ⟨T,g,P,G,hg,hP0,hPmono,haff,hGne,hGpos,hGgcd,hPgap,hrec⟩ :=
    normalized_walk hd₁ hgaps
  have hcov := hcases P G hP0 hPmono hGne
    (fun x hx => ⟨(hGpos x hx).1,(hGpos x hx).2.trans hd₂⟩)
    hGgcd hPgap hrec
  exact tailCovering_of_rescaled T g (a T) hg P haff hcov

end Erdos1112.Proof.Short
