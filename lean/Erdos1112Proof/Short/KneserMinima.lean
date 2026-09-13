/-
Weak-Kneser plan step 4 (`/tmp/erdos1112-agents/WEAK_KNESER_PLAN.md`):
fixed residue classes and minima under ordinary `e`-transforms.

"A_n has a fixed set of residue classes modulo g: ordinary e-transforms add
only e+b with e already in A_n and g dividing b. The minimum r_j of each
represented class also stays fixed, since e+b>=e."

For `g > 0`, `B` a set of multiples of `g`, and `e ∈ A`, the ordinary
`e`-transform `eA A B e = A ∪ (B + e)`
(`Short/KneserDensity/ETransform.lean`) has *exactly* the same set of
residues mod `g` as `A`, and the same minimum in every represented residue
class. This is lifted to the concrete ordinary-transform sequence
`Aseq`/`Bseq` (`Short/KneserConcrete.lean`, read-only import here, not
edited): once `Bseq A B N` consists of multiples of `g`, every later
`Aseq A B n` (`n ≥ N`) has the same residues mod `g` and the same class
minima as `Aseq A B N`. `Bseq` is antitone, so "multiples of `g` at `N`"
propagates to every later stage for free — no extra hypothesis on `n > N`
is needed, matching the task's framing of a single stabilization stage `N`.

Only natural-number, nonnegative reasoning throughout (no signed
coefficients): the invariance rests entirely on `e + b ≥ e` and `g ∣ b`.

Owns only this file. `KneserConcrete.lean`, `KneserSequence.lean`, and
`KneserDensity/ETransform.lean` are read-only imports (their `Aseq`, `Bseq`,
`eA`, `eB`, `Unresolved`, `transformNext`, `Bseq_antitone`), never edited.
`KneserCompression.lean` (a different worker's file) is untouched and
unimported. No `sorry`, no custom axiom.
-/
import Erdos1112Proof.Short.KneserConcrete

namespace Erdos1112.Proof.Short.KneserDensity

/-! ### The residue-class invariants -/

/-- The set of residues mod `g` realized by `A`. -/
def residues (A : Set ℕ) (g : ℕ) : Set ℕ := {r | ∃ a ∈ A, a % g = r}

/-- The least element of `A` in residue class `r` mod `g`
(junk `0` if the class is empty, per `Nat.sInf`'s convention). -/
noncomputable def classMin (A : Set ℕ) (g r : ℕ) : ℕ := sInf {a ∈ A | a % g = r}

/-! ### The single-step invariance: the algebraic core of step 4 -/

/-- If `g ∣ b`, adding `b` to `e` never changes the residue class:
`(b + e) % g = e % g`. -/
private lemma add_mod_of_dvd {g b e : ℕ} (hb : g ∣ b) : (b + e) % g = e % g := by
  obtain ⟨k, rfl⟩ := hb
  have h0 : g * k ≡ 0 [MOD g] := (Nat.modEq_zero_iff_dvd).mpr ⟨k, rfl⟩
  simpa using h0.add_right e

/-- **Same represented residues.** For `g > 0`, `B` a set of multiples of
`g`, and `e ∈ A`, the `e`-transform `eA A B e = A ∪ (B + e)` represents
exactly the same residues mod `g` as `A`: the new elements `b + e` all fall
in `e`'s own class, already represented by `A` since `e ∈ A`. -/
theorem residues_eA_eq {g : ℕ} (hg : 0 < g) {A B : Set ℕ} (hB : ∀ b ∈ B, g ∣ b)
    {e : ℕ} (he : e ∈ A) : residues (eA A B e) g = residues A g := by
  ext r
  simp only [residues, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases mem_eA_iff.mp ha with haA | ⟨b, hb, rfl⟩
    · exact ⟨a, haA, rfl⟩
    · exact ⟨e, he, (add_mod_of_dvd (hB b hb)).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, subset_eA A B e ha, rfl⟩

/-- **Same class minima.** For `g > 0`, `B` a set of multiples of `g`, and
`e ∈ A`, the `e`-transform does not change the least element of any residue
class mod `g`: every new element `b + e` (`b ∈ B`) satisfies `b + e ≥ e`,
and `e` is already in `A`'s class, so it cannot lower the minimum there;
other classes are untouched entirely. Pure natural-number reasoning, no
signed coefficients. -/
theorem classMin_eA_eq {g : ℕ} (hg : 0 < g) {A B : Set ℕ} (hB : ∀ b ∈ B, g ∣ b)
    {e : ℕ} (he : e ∈ A) (r : ℕ) : classMin (eA A B e) g r = classMin A g r := by
  unfold classMin
  by_cases hr : r = e % g
  · subst hr
    have hAsub : {a ∈ A | a % g = e % g} ⊆ {a ∈ eA A B e | a % g = e % g} :=
      fun a ha => ⟨subset_eA A B e ha.1, ha.2⟩
    have heA : e ∈ {a ∈ A | a % g = e % g} := ⟨he, rfl⟩
    have hAne : {a ∈ A | a % g = e % g}.Nonempty := ⟨e, heA⟩
    have heEA : e ∈ {a ∈ eA A B e | a % g = e % g} := ⟨subset_eA A B e he, rfl⟩
    have hEAne : {a ∈ eA A B e | a % g = e % g}.Nonempty := ⟨e, heEA⟩
    apply le_antisymm
    · exact Nat.sInf_le (hAsub (Nat.sInf_mem hAne))
    · obtain ⟨haEA, har⟩ := Nat.sInf_mem hEAne
      rcases mem_eA_iff.mp haEA with haA | ⟨b, hb, hba⟩
      · exact Nat.sInf_le (m := sInf {a ∈ eA A B e | a % g = e % g}) ⟨haA, har⟩
      · have hle : sInf {a ∈ A | a % g = e % g} ≤ e := Nat.sInf_le heA
        have : e ≤ sInf {a ∈ eA A B e | a % g = e % g} := by
          rw [← hba]; omega
        omega
  · have hset : {a ∈ eA A B e | a % g = r} = {a ∈ A | a % g = r} := by
      ext a
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨ha, har⟩
        rcases mem_eA_iff.mp ha with haA | ⟨b, hb, rfl⟩
        · exact ⟨haA, har⟩
        · exact absurd (har.symm.trans (add_mod_of_dvd (hB b hb))) hr
      · rintro ⟨haA, har⟩
        exact ⟨subset_eA A B e haA, har⟩
    rw [hset]

/-! ### Lifted to `transformNext eStep` -/

theorem residues_transformNext_eq {g : ℕ} (hg : 0 < g) (s : PairState)
    (hB : ∀ b ∈ s.2, g ∣ b) :
    residues (transformNext eStep s).1 g = residues s.1 g := by
  classical
  by_cases h : ∃ e, Unresolved s e
  · have he := (leastUnresolved_spec h).1
    have hs : (transformNext eStep s).1 = eA s.1 s.2 (leastUnresolved s) := by
      unfold transformNext; rw [if_pos h]; rfl
    rw [hs]
    exact residues_eA_eq hg hB he
  · unfold transformNext; rw [if_neg h]

theorem classMin_transformNext_eq {g : ℕ} (hg : 0 < g) (s : PairState)
    (hB : ∀ b ∈ s.2, g ∣ b) (r : ℕ) :
    classMin (transformNext eStep s).1 g r = classMin s.1 g r := by
  classical
  by_cases h : ∃ e, Unresolved s e
  · have he := (leastUnresolved_spec h).1
    have hs : (transformNext eStep s).1 = eA s.1 s.2 (leastUnresolved s) := by
      unfold transformNext; rw [if_pos h]; rfl
    rw [hs]
    exact classMin_eA_eq hg hB he r
  · unfold transformNext; rw [if_neg h]

/-! ### Lifted to the sequence `Aseq A B`, `Bseq A B`

Once `Bseq A B N` consists of multiples of `g`, so does `Bseq A B n` for
every `n ≥ N` (`Bseq` is antitone, so `Bseq A B n ⊆ Bseq A B N`), and the
residue classes and their minima in `Aseq A B n` therefore stay fixed at
their value at stage `N`, for every `n ≥ N`. -/

theorem residues_Aseq_eq_of_multiples {g : ℕ} (hg : 0 < g) (A B : Set ℕ) {N : ℕ}
    (hBN : ∀ b ∈ Bseq A B N, g ∣ b) :
    ∀ n ≥ N, residues (Aseq A B n) g = residues (Aseq A B N) g := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hBn : ∀ b ∈ Bseq A B n, g ∣ b := fun b hb => hBN b (Bseq_antitone A B hn hb)
    have heq : Aseq A B (n + 1) = (transformNext eStep (Aseq A B n, Bseq A B n)).1 := rfl
    rw [heq, residues_transformNext_eq hg (Aseq A B n, Bseq A B n) hBn, ih]

theorem classMin_Aseq_eq_of_multiples {g : ℕ} (hg : 0 < g) (A B : Set ℕ) {N : ℕ}
    (hBN : ∀ b ∈ Bseq A B N, g ∣ b) (r : ℕ) :
    ∀ n ≥ N, classMin (Aseq A B n) g r = classMin (Aseq A B N) g r := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hBn : ∀ b ∈ Bseq A B n, g ∣ b := fun b hb => hBN b (Bseq_antitone A B hn hb)
    have heq : Aseq A B (n + 1) = (transformNext eStep (Aseq A B n, Bseq A B n)).1 := rfl
    rw [heq, classMin_transformNext_eq hg (Aseq A B n, Bseq A B n) hBn r, ih]

end Erdos1112.Proof.Short.KneserDensity
