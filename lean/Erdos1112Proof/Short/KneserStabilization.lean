/- Finite stabilization lemmas for the "weak Kneser via ordinary e-transforms"
route (`/tmp/erdos1112-agents/WEAK_KNESER_PLAN.md`, step 2–3).

Given an antitone sequence `B : ℕ → Set ℕ` with `0 ∈ B n` and a positive
element in every `B n` (the case `B n = {0}` is handled elsewhere, per the
plan — it is excluded here by hypothesis, not derived):

1. `gapMin (B n)`, the least positive gap between two elements of `B n`, is
   positive, is attained by an actual pair, separates every pair of `B n`,
   and is monotone (nondecreasing) in `n` (`B` antitone ⟹ fewer candidate
   pairs ⟹ gaps only grow). A bounded monotone `ℕ`-sequence is either
   unbounded or eventually constant (`monotone_dichotomy`, generic).
2. Once the gap stabilizes at a fixed `f > 0` from some point on, the
   residue alphabet `residueAlphabet B f n = {b % f : b ∈ B n}` is antitone
   under `⊆` and — being a `Finset ℕ` sequence antitone under `⊆` — stabilizes
   by a finite-cardinality-decline argument (`antitone_finset_stabilizes`,
   generic, not specific to residues).
3. For the stable residue alphabet `R`, `g := gcd (insert f R)` is positive,
   divides `f`, divides every element of every later `B n` (a `b % f ∈ R`
   representative combined with `b = f·(b/f) + b%f`), and the normalized
   finite alphabet `insert (f/g) (R.image (·/g))` has gcd `1`
   (`Finset.gcd_div_id_eq_one` transported through `Finset.gcd_eq_gcd_image`
   and `Finset.image_insert` — no need for `Short.Normalization`'s bundled
   `normalized_alphabet`, whose `∀x∈G,0<x` hypothesis fails here since `0`
   is always a represented residue).

Every conclusion is a concrete `Set`/`Finset` fact (an actual minimum, an
actual stabilization index, an actual gcd), not an abstract convergence
assumption — exactly what the plan's compression step (5) needs to consume.

Pure `ℕ`/finite-set combinatorics throughout; no density/analytic content
(that lives in `Short/KneserDensity/*` and `Short/DensityIteration.lean`,
owned elsewhere). No `sorry`, no custom axioms. -/
import Mathlib

namespace Erdos1112.Proof.Short

open scoped Classical

/-! ### 1. The minimum gap of a set -/

/-- The set of positive gaps realized by some pair of `S` (`x ∈ S`,
`x + d ∈ S`, `d > 0`). -/
def gapSet (S : Set ℕ) : Set ℕ := {d | 0 < d ∧ ∃ x ∈ S, x + d ∈ S}

/-- The least positive gap between two elements of `S`. -/
noncomputable def gapMin (S : Set ℕ) : ℕ := sInf (gapSet S)

/-- `gapSet S` is nonempty whenever `S` contains `0` and a positive element
`p` (the gap `p - 0 = p` is realized). -/
lemma gapSet_nonempty {S : Set ℕ} {p : ℕ} (h0 : (0 : ℕ) ∈ S) (hp : p ∈ S) (hppos : 0 < p) :
    (gapSet S).Nonempty :=
  ⟨p, hppos, 0, h0, by simpa using hp⟩

/-- **Pair attainment**: `gapMin S` is itself a realized gap. -/
lemma gapMin_mem {S : Set ℕ} (hne : (gapSet S).Nonempty) : gapMin S ∈ gapSet S :=
  Nat.sInf_mem hne

/-- **Positivity**: `gapMin S > 0`. -/
lemma gapMin_pos {S : Set ℕ} (hne : (gapSet S).Nonempty) : 0 < gapMin S :=
  (gapMin_mem hne).1

/-- **Pair attainment**, unpacked: some `x ∈ S` has `x + gapMin S ∈ S`. -/
lemma gapMin_pair {S : Set ℕ} (hne : (gapSet S).Nonempty) :
    ∃ x ∈ S, x + gapMin S ∈ S := (gapMin_mem hne).2

/-- **Separation**: every pair of distinct elements of `S` is at least
`gapMin S` apart. -/
lemma le_gapMin {S : Set ℕ} {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
    gapMin S ≤ y - x := by
  apply Nat.sInf_le
  refine ⟨by omega, x, hx, ?_⟩
  have hxy' : x + (y - x) = y := by omega
  rwa [hxy']

lemma gapSet_mono {S T : Set ℕ} (h : S ⊆ T) : gapSet S ⊆ gapSet T := by
  rintro d ⟨hd, x, hx, hxd⟩
  exact ⟨hd, x, h hx, h hxd⟩

/-- **Monotonicity**: for `B` antitone (`B (n+1) ⊆ B n`), `gapMin (B n)` is
nondecreasing in `n` (a shrinking candidate set has no smaller gaps). -/
theorem gapMin_monotone {B : ℕ → Set ℕ} (hanti : ∀ n, B (n + 1) ⊆ B n)
    (hne : ∀ n, (gapSet (B n)).Nonempty) :
    Monotone (fun n => gapMin (B n)) := by
  apply monotone_nat_of_le_succ
  intro n
  have hsub : gapSet (B (n + 1)) ⊆ gapSet (B n) := gapSet_mono (hanti n)
  have hmem : gapMin (B (n + 1)) ∈ gapSet (B (n + 1)) := gapMin_mem (hne (n + 1))
  exact Nat.sInf_le (hsub hmem)

/-! ### 2. Bounded-monotone dichotomy and finite-alphabet stabilization

Both are generic facts about `ℕ`-sequences / `Finset ℕ`-sequences, stated
without reference to `gapMin` or residues, since they are reused for both. -/

/-- **Dichotomy**: a monotone (nondecreasing) `ℕ`-valued sequence is either
unbounded, or eventually constant. -/
theorem monotone_dichotomy {f : ℕ → ℕ} (hmono : Monotone f) :
    (∀ M, ∃ n, M ≤ f n) ∨ ∃ N c, ∀ n, N ≤ n → f n = c := by
  by_cases hub : ∀ M, ∃ n, M ≤ f n
  · exact Or.inl hub
  · right
    push_neg at hub
    obtain ⟨M, hM⟩ := hub
    have hbdd : BddAbove (Set.range f) := ⟨M, by rintro _ ⟨n, rfl⟩; exact (hM n).le⟩
    have hne : (Set.range f).Nonempty := ⟨f 0, 0, rfl⟩
    obtain ⟨N, hN⟩ := Nat.sSup_mem hne hbdd
    refine ⟨N, sSup (Set.range f), fun n hn => ?_⟩
    have h1 : f N ≤ f n := hmono hn
    have h2 : f n ≤ sSup (Set.range f) := le_csSup hbdd ⟨n, rfl⟩
    omega

theorem antitone_step_le {R : ℕ → Finset ℕ} (hanti : ∀ n, R (n + 1) ⊆ R n) {m : ℕ} :
    ∀ n, m ≤ n → R n ⊆ R m := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ n _ ih => exact (hanti n).trans ih

/-- **Finite-cardinality-decline stabilization**: a `Finset ℕ`-valued
sequence antitone under `⊆` stabilizes (its card is nonincreasing and
bounded below by `0`, hence eventually constant; equal card plus `⊆`
forces equality). -/
theorem antitone_finset_stabilizes {R : ℕ → Finset ℕ} (hanti : ∀ n, R (n + 1) ⊆ R n) :
    ∃ N, ∀ n, N ≤ n → R n = R N := by
  have hne : (Set.range (fun n => (R n).card)).Nonempty := ⟨(R 0).card, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.sInf_mem hne
  dsimp only at hN
  refine ⟨N, fun n hn => ?_⟩
  have hsub : R n ⊆ R N := antitone_step_le hanti n hn
  have hle1 : (R n).card ≤ (R N).card := Finset.card_le_card hsub
  have hle2 : sInf (Set.range (fun n => (R n).card)) ≤ (R n).card := Nat.sInf_le ⟨n, rfl⟩
  have heqcard : (R n).card = (R N).card := by omega
  exact Finset.eq_of_subset_of_card_le hsub heqcard.ge

/-! ### 3. The residue alphabet modulo a stable gap -/

/-- The residues mod `f` represented by `B n`. -/
noncomputable def residueAlphabet (B : ℕ → Set ℕ) (f : ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range f).filter (fun r => ∃ b ∈ B n, b % f = r)

lemma residueAlphabet_subset_range (B : ℕ → Set ℕ) (f n : ℕ) :
    residueAlphabet B f n ⊆ Finset.range f := Finset.filter_subset _ _

/-- **Antitone**: `B` antitone gives `residueAlphabet B f` antitone. -/
theorem residueAlphabet_antitone {B : ℕ → Set ℕ} (hanti : ∀ n, B (n + 1) ⊆ B n) (f : ℕ) :
    ∀ n, residueAlphabet B f (n + 1) ⊆ residueAlphabet B f n := by
  intro n r hr
  simp only [residueAlphabet, Finset.mem_filter] at hr ⊢
  obtain ⟨hrange, b, hb, hbr⟩ := hr
  exact ⟨hrange, b, hanti n hb, hbr⟩

lemma mem_residueAlphabet {B : ℕ → Set ℕ} {f n r : ℕ} (hf : 0 < f) {b : ℕ}
    (hb : b ∈ B n) (hbr : b % f = r) : r ∈ residueAlphabet B f n := by
  simp only [residueAlphabet, Finset.mem_filter, Finset.mem_range]
  exact ⟨hbr ▸ Nat.mod_lt b hf, b, hb, hbr⟩

/-- **Residue alphabet stabilizes**: an instance of
`antitone_finset_stabilizes`, spelled out for `residueAlphabet`. -/
theorem residueAlphabet_stabilizes {B : ℕ → Set ℕ} (hanti : ∀ n, B (n + 1) ⊆ B n) (f : ℕ) :
    ∃ N, ∀ n, N ≤ n → residueAlphabet B f n = residueAlphabet B f N :=
  antitone_finset_stabilizes (residueAlphabet_antitone hanti f)

/-! ### 4. The finite gcd normalization -/

lemma nat_mod_representation (b f : ℕ) : b = f * (b / f) + b % f := (Nat.div_add_mod b f).symm

/-- `g := gcd (insert f R)` is positive (it divides `f > 0`, and a natural
number dividing a positive number is itself positive unless it is `0`,
which is excluded since `0 ∣ f` would force `f = 0`). -/
theorem stable_gcd_pos {f : ℕ} {R : Finset ℕ} (hf : 0 < f) :
    0 < (insert f R).gcd id := by
  rcases Nat.eq_zero_or_pos ((insert f R).gcd id) with h0 | h0
  · exfalso
    have hdvd : (insert f R).gcd id ∣ f := Finset.gcd_dvd (Finset.mem_insert_self f R)
    rw [h0, zero_dvd_iff] at hdvd
    omega
  · exact h0

theorem stable_gcd_dvd_f {f : ℕ} {R : Finset ℕ} : (insert f R).gcd id ∣ f :=
  Finset.gcd_dvd (Finset.mem_insert_self f R)

theorem stable_gcd_dvd_of_mem {f : ℕ} {R : Finset ℕ} {r : ℕ} (hr : r ∈ R) :
    (insert f R).gcd id ∣ r :=
  Finset.gcd_dvd (Finset.mem_insert_of_mem hr)

/-- **`g` divides every element of `B n`** (once `f` is the actual gap of
`B n` and `residueAlphabet B f n` is its residue alphabet): `b`'s residue
`b % f` is represented, hence divisible by `g`, and `g ∣ f` gives `g ∣ b`
via `b = f·(b/f) + b%f`. -/
theorem stable_gcd_dvd_B {B : ℕ → Set ℕ} {f n : ℕ} (hf : 0 < f) {b : ℕ}
    (hb : b ∈ B n) :
    (insert f (residueAlphabet B f n)).gcd id ∣ b := by
  have hmem : b % f ∈ residueAlphabet B f n := mem_residueAlphabet hf hb rfl
  have h1 : (insert f (residueAlphabet B f n)).gcd id ∣ f := stable_gcd_dvd_f
  have h2 : (insert f (residueAlphabet B f n)).gcd id ∣ b % f := stable_gcd_dvd_of_mem hmem
  rw [nat_mod_representation b f]
  exact Nat.dvd_add (Dvd.dvd.mul_right h1 (b / f)) h2

/-- **`g` divides every element of every later `B n`**, given the residue
alphabet has already stabilized to `R` at `N`. -/
theorem stable_gcd_dvd_B_from {B : ℕ → Set ℕ} {f N : ℕ} (hf : 0 < f)
    (hstable : ∀ n, N ≤ n → residueAlphabet B f n = residueAlphabet B f N) :
    ∀ n, N ≤ n → ∀ b ∈ B n, (insert f (residueAlphabet B f N)).gcd id ∣ b := by
  intro n hn b hb
  rw [← hstable n hn]
  exact stable_gcd_dvd_B hf hb

/-- **Normalization**: the finite alphabet `insert (f/g) (R.image (·/g))`
(`g := gcd (insert f R)`) has gcd `1`. Built from `Finset.gcd_div_id_eq_one`
(needs only *one* nonzero element of `insert f R`, namely `f`, unlike
`Short.Normalization.normalized_alphabet`, whose stronger `∀x∈G,0<x`
hypothesis fails here — `0` is always a represented residue, since `0 ∈ B
n` for every `n`). -/
theorem stable_gcd_normalized {f : ℕ} {R : Finset ℕ} (hf : 0 < f) :
    (insert (f / (insert f R).gcd id) (R.image (· / (insert f R).gcd id))).gcd id = 1 := by
  have h1 := Finset.gcd_div_id_eq_one (s := insert f R) (Finset.mem_insert_self f R) hf.ne'
  rwa [Finset.gcd_eq_gcd_image, Finset.image_insert] at h1

/-! ### 5. The bundled stabilization interface

What the compression step of the plan actually consumes: an explicit
stabilization index `N`, the stable gap `f`, the stable residue alphabet
`R`, and the four `g`-facts, all as concrete data (no abstract convergence
statement). Obtained from `monotone_dichotomy` (applied to `gapMin_monotone`)
ruling out the unbounded branch, then `residueAlphabet_stabilizes`. -/

/-- **The stabilization bundle.** For `B` antitone with `0 ∈ B n` and a
positive element in every `B n`: either `gapMin (B n)` is unbounded, or it
stabilizes to a fixed `f > 0` from some point `N` on, at which point the
residue alphabet also stabilizes (to `R`, from some later point `N' ≥ N`
on), and `g := gcd (insert f R)` is a positive common divisor of `f` and of
every element of every `B n` (`n ≥ N'`), normalized so that the alphabet
`insert (f/g) (R.image (·/g))` has gcd `1`. -/
theorem stabilization_bundle {B : ℕ → Set ℕ} (hanti : ∀ n, B (n + 1) ⊆ B n)
    (h0 : ∀ n, (0 : ℕ) ∈ B n) (hpos : ∀ n, ∃ p ∈ B n, 0 < p) :
    (∀ M, ∃ n, M ≤ gapMin (B n)) ∨
      ∃ N f, 0 < f ∧ (∀ n, N ≤ n → gapMin (B n) = f) ∧
        ∃ N', N ≤ N' ∧ ∃ R : Finset ℕ,
          (∀ n, N' ≤ n → residueAlphabet B f n = R) ∧
          (0 < (insert f R).gcd id ∧ (insert f R).gcd id ∣ f ∧
            (∀ n, N' ≤ n → ∀ b ∈ B n, (insert f R).gcd id ∣ b) ∧
            (insert (f / (insert f R).gcd id) (R.image (· / (insert f R).gcd id))).gcd id
              = 1) := by
  have hne : ∀ n, (gapSet (B n)).Nonempty := by
    intro n
    obtain ⟨p, hp, hppos⟩ := hpos n
    exact gapSet_nonempty (h0 n) hp hppos
  rcases monotone_dichotomy (gapMin_monotone hanti hne) with hunb | ⟨N, f, hstab⟩
  · exact Or.inl hunb
  · right
    have hfpos : 0 < f := by
      have := hstab N le_rfl
      have hne' := gapMin_pos (hne N)
      omega
    obtain ⟨N', hN'⟩ := residueAlphabet_stabilizes hanti f
    refine ⟨N, f, hfpos, hstab, max N N', le_max_left _ _, residueAlphabet B f N', ?_, ?_⟩
    · intro n hn
      exact hN' n (le_trans (le_max_right N N') hn)
    · refine ⟨stable_gcd_pos hfpos, stable_gcd_dvd_f, ?_, stable_gcd_normalized hfpos⟩
      intro n hn b hb
      exact stable_gcd_dvd_B_from hfpos hN' n (le_trans (le_max_right N N') hn) b hb

end Erdos1112.Proof.Short
