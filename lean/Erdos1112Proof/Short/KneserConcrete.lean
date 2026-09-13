/-
The concrete instantiation of the abstract fair-transform sequence
(`Short/KneserSequence.lean`) by the ordinary `e`-transform
(`Short/KneserDensity/ETransform.lean`), for the density route documented
in `Short/KneserDensity/README.md`: ordinary `e`-transforms suffice for the
route to the weak pairwise Kneser law `hkn` (`Short/DensityIteration.lean`)
— no maximal-pair construction and no `B*` case split are needed. This
file supplies:

* `eStep`, the ordinary `e`-transform packaged as a `PairState` step, and a
  proof that it satisfies `TransformLaws`;
* the concrete sequence `Aseq A B`, `Bseq A B` (via `transformSequence`),
  with `0`-membership, monotonicity/antitonicity, fairness, sumset
  containment in `A + B`, and *constant* joint density `δ(A_n,B_n) = δ(A,B)`
  (via `twoFoldLowerDensity_eTransform_eq`);
* the resolution of the `B_n = {0}` case: it already gives
  `δ(A,B) ≤ δ(A+B)`, one whole disjunct of `hkn`;
* a spacing count bound and its density consequence for `Bseq A B n`
  directly (`spacing_mul_posCount_le`,
  `twoFoldLowerDensity_le_lowerDensity_add_add_inv_of_spacing`), the density
  half of the unbounded minimum-gap alternative for this concrete sequence.

The remaining case (`B_n ≠ {0}` for every `n`) needs the min-gap/residue
dichotomy and block-growth argument (`Short/KneserStabilization.lean`,
`Short/KneserCompression.lean`, `Short/KneserResidues.lean`,
`Short/KneserBlockSequence.lean`); this file does not duplicate that.
-/
import Mathlib
import Erdos1112Proof.Short.KneserDensity.ETransform
import Erdos1112Proof.Short.KneserSequence
import Erdos1112Proof.Short.DensityIteration

namespace Erdos1112.Proof.Short.KneserDensity

open scoped Pointwise Classical

/-! ### The ordinary `e`-transform as a `PairState` step -/

/-- The ordinary `e`-transform, packaged as a `PairState → ℕ → PairState`
step for `KneserSequence.transformSequence`. -/
def eStep (s : PairState) (e : ℕ) : PairState := (eA s.1 s.2 e, eB s.1 s.2 e)

/-- The ordinary `e`-transform satisfies the abstract `TransformLaws`
(all three clauses hold *unconditionally*, without even needing
`Unresolved`: this is exactly Theorem 4, parts I and the `B'` absorption
fact from Definition 3). -/
theorem eStep_laws : TransformLaws eStep where
  left := fun s _ _ => subset_eA s.1 s.2 _
  right := fun s _ _ => eB_subset s.1 s.2 _
  absorbs := fun s _ _ b hb => mem_eA_iff.mpr (Or.inr ⟨b, eB_subset s.1 s.2 _ hb, by ring⟩)

/-- The ordinary `e`-transform's sumset containment (Theorem 4, part II),
unconditionally, in the shape `transformSequence_sum_subset` expects. -/
theorem eStep_sum_subset : ∀ s e, Unresolved s e → (eStep s e).1 + (eStep s e).2 ⊆ s.1 + s.2 :=
  fun s e _ => add_eA_eB_subset s.1 s.2 e

/-- If `e ∈ s.1` (in particular whenever `Unresolved s e`) and `0 ∈ s.2`,
the transform keeps `0` in the second component: `0 + e = e ∈ s.1`. -/
theorem eStep_zero_mem_snd {s : PairState} {e : ℕ} (he : e ∈ s.1) (h0 : 0 ∈ s.2) :
    0 ∈ (eStep s e).2 :=
  mem_eB_iff.mpr ⟨h0, by simpa using he⟩

/-! ### The concrete sequence `Aseq A B`, `Bseq A B` -/

/-- The `n`-th first component of the ordinary `e`-transform sequence
started from `(A, B)`. -/
noncomputable def Aseq (A B : Set ℕ) (n : ℕ) : Set ℕ := (transformSequence eStep (A, B) n).1

/-- The `n`-th second component of the ordinary `e`-transform sequence
started from `(A, B)`. -/
noncomputable def Bseq (A B : Set ℕ) (n : ℕ) : Set ℕ := (transformSequence eStep (A, B) n).2

@[simp] lemma Aseq_zero (A B : Set ℕ) : Aseq A B 0 = A := rfl
@[simp] lemma Bseq_zero (A B : Set ℕ) : Bseq A B 0 = B := rfl

theorem Aseq_monotone (A B : Set ℕ) : Monotone (Aseq A B) := sequence_left_mono eStep_laws (A, B)

theorem Bseq_antitone (A B : Set ℕ) : Antitone (Bseq A B) := sequence_right_anti eStep_laws (A, B)

/-- `0 ∈ A` propagates to every `Aseq A B n` (monotonicity plus `0 ∈ A`). -/
theorem zero_mem_Aseq {A B : Set ℕ} (hA : 0 ∈ A) (n : ℕ) : 0 ∈ Aseq A B n :=
  Aseq_monotone A B (Nat.zero_le n) (by simpa using hA)

/-- `0 ∈ B` propagates to every `Bseq A B n`: an induction using
`eStep_zero_mem_snd` at each active step (this is genuinely inductive,
unlike the first component — `Bseq` is *antitone*, so membership is not
automatic from `0 ∈ B` alone without knowing the transform never removes
`0`). -/
theorem zero_mem_Bseq {A B : Set ℕ} (hB : 0 ∈ B) : ∀ n, 0 ∈ Bseq A B n := by
  intro n
  induction n with
  | zero => simpa [Bseq] using hB
  | succ n ih =>
    by_cases h : ∃ e, Unresolved (transformSequence eStep (A, B) n) e
    · simpa [Bseq, transformSequence, transformNext, h] using
        eStep_zero_mem_snd (leastUnresolved_spec h).1 ih
    · simpa [Bseq, transformSequence, transformNext, h] using ih

/-- Fair absorption of the concrete sequence (Root's `KneserSequence`
machinery, instantiated). -/
theorem fair_Aseq_Bseq (A B : Set ℕ) : FairAbsorption (Aseq A B) (Bseq A B) :=
  transformSequence_fair eStep_laws (A, B)

/-- The sumset never leaves the original `A + B`. -/
theorem Aseq_add_Bseq_subset (A B : Set ℕ) (n : ℕ) : Aseq A B n + Bseq A B n ⊆ A + B :=
  transformSequence_sum_subset eStep_sum_subset (A, B) n

/-! ### The joint density `δ(A_n,B_n)` is constant -/

set_option maxHeartbeats 1000000 in
theorem twoFoldLowerDensity_Aseq_Bseq_ge (A B : Set ℕ) (n : ℕ) :
    twoFoldLowerDensity A B ≤ twoFoldLowerDensity (Aseq A B n) (Bseq A B n) := by
  have hφ : ∀ s : PairState, ∀ e, Unresolved s e →
      (fun s : PairState => twoFoldLowerDensity s.1 s.2) s ≤
        (fun s : PairState => twoFoldLowerDensity s.1 s.2) (eStep s e) :=
    fun s e _ => (twoFoldLowerDensity_eTransform_eq s.1 s.2 e).le
  exact transformSequence_score hφ (A, B) n

set_option maxHeartbeats 1000000 in
theorem twoFoldLowerDensity_Aseq_Bseq_le (A B : Set ℕ) (n : ℕ) :
    twoFoldLowerDensity (Aseq A B n) (Bseq A B n) ≤ twoFoldLowerDensity A B := by
  have hφ : ∀ s : PairState, ∀ e, Unresolved s e →
      (fun s : PairState => -twoFoldLowerDensity s.1 s.2) s ≤
        (fun s : PairState => -twoFoldLowerDensity s.1 s.2) (eStep s e) :=
    fun s e _ => neg_le_neg (twoFoldLowerDensity_eTransform_eq s.1 s.2 e).ge
  have h := transformSequence_score hφ (A, B) n
  simpa using h

/-- The joint density `δ(A_n,B_n)` is *constant* along the sequence, equal
to `δ(A,B)`: an `e`-transform never changes it (Theorem 5), so neither does
any number of iterations. -/
theorem twoFoldLowerDensity_Aseq_Bseq (A B : Set ℕ) (n : ℕ) :
    twoFoldLowerDensity (Aseq A B n) (Bseq A B n) = twoFoldLowerDensity A B :=
  le_antisymm (twoFoldLowerDensity_Aseq_Bseq_le A B n) (twoFoldLowerDensity_Aseq_Bseq_ge A B n)

/-! ### The `Bseq A B n = {0}` case already gives `δ(A,B) ≤ δ(A+B)` -/

private lemma posCount_singleton_zero (n : ℕ) : posCount ({0} : Set ℕ) n = 0 := by
  have hempty : (({0} : Set ℕ) ∩ Set.Icc 1 n) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_Icc, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨rfl, h1, -⟩
    omega
  unfold posCount
  rw [hempty, Set.ncard_empty]

private lemma twoFoldLowerDensity_singleton_zero (A : Set ℕ) :
    twoFoldLowerDensity A ({0} : Set ℕ) = lowerDensity A := by
  have hfun : (fun n : ℕ => ((posCount A n : ℝ) + posCount ({0} : Set ℕ) n) / n) =
      fun n : ℕ => (posCount A n : ℝ) / n := by
    funext n; rw [posCount_singleton_zero]; ring
  unfold twoFoldLowerDensity lowerDensity
  rw [hfun]

/-- **The `B_n = {0}` resolution.** If the second component ever collapses
to `{0}`, the joint density is already transferred to `A + B` outright:
`δ(A,B) = δ(A_n,B_n) = δ(A_n) = δ(A_n + {0}) ≤ δ(A+B)`. This is exactly one
disjunct of `hkn` (`Short/DensityIteration.lean`); the other disjunct
(`HasAPTail (A+B)`) is for the `B_n ≠ {0}` (min-gap/residue/block) route to
supply. -/
theorem twoFoldLowerDensity_le_lowerDensity_add_of_snd_eq_zero
    {A B : Set ℕ} {n : ℕ} (h0 : Bseq A B n = {0}) :
    twoFoldLowerDensity A B ≤ lowerDensity (A + B) := by
  have heq : twoFoldLowerDensity A B = twoFoldLowerDensity (Aseq A B n) (Bseq A B n) :=
    (twoFoldLowerDensity_Aseq_Bseq A B n).symm
  rw [heq, h0, twoFoldLowerDensity_singleton_zero]
  have hsub : Aseq A B n + ({0} : Set ℕ) ⊆ A + B := h0 ▸ Aseq_add_Bseq_subset A B n
  have hsum : Aseq A B n + ({0} : Set ℕ) = Aseq A B n := by simp
  exact Erdos1112.Proof.Short.lowerDensity_mono (hsum ▸ hsub)

/-! ### Optional: the generic spacing/density bound (`WEAK_KNESER_PLAN.md` step 2)

This supplies only the *static* combinatorial fact "spacing `≥ F` in a set
`B` containing `0` forces `posCount B N ≤ N / F`" and its density
consequence. It does **not** define or stabilize any `n`-indexed min-gap
sequence `f_n` — that tracking is a different worker's task (see the file
header) — this is deliberately just a one-shot bound consuming an
arbitrary spacing witness `F`, to be applied at whatever `n` that worker's
argument selects. -/

/-- If `B` contains `0` and every two distinct elements of `B` are at least
`F ≥ 1` apart, `posCount B` grows at rate at most `1/F`: `F * posCount B N
≤ N` for every `N`. Proved by strong induction on `N`, using that the
window `(N-F, N]` contains at most one element of `B` (two would violate
spacing) to reduce to `N - F`. -/
theorem spacing_mul_posCount_le {B : Set ℕ} {F : ℕ} (hF : 0 < F) (h0 : 0 ∈ B)
    (hspace : ∀ x ∈ B, ∀ y ∈ B, x < y → F ≤ y - x) :
    ∀ N, F * posCount B N ≤ N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N F with hNF | hNF
    · have hempty : B ∩ Set.Icc 1 N = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hxB, hx1, hx2⟩
        have := hspace 0 h0 x hxB (by omega)
        omega
      have : posCount B N = 0 := by unfold posCount; rw [hempty, Set.ncard_empty]
      simp [this]
    · have hle : N - F ≤ N := by omega
      have hwin : posCount B N ≤ posCount B (N - F) + 1 := by
        rw [posCount_window_add B hle]
        have hcard : (B ∩ Set.Icc (N - F + 1) N).ncard ≤ 1 := by
          rw [Set.ncard_le_one ((Set.finite_Icc _ _).inter_of_right _)]
          rintro x ⟨hxB, hx1, hx2⟩ y ⟨hyB, hy1, hy2⟩
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hsp := hspace x hxB y hyB hlt; omega
          · have hsp := hspace y hyB x hxB hgt; omega
        omega
      have hFN : N - F < N := by omega
      have hind := ih (N - F) hFN
      calc F * posCount B N ≤ F * (posCount B (N - F) + 1) := by
            exact Nat.mul_le_mul_left F hwin
        _ = F * posCount B (N - F) + F := by ring
        _ ≤ (N - F) + F := by omega
        _ = N := by omega

/-- The density consequence of `spacing_mul_posCount_le`: a spacing witness
`F` for `Bseq A B n` bounds the joint-density gap by `1/F`, i.e.
`δ(A,B) ≤ δ(A_n) + 1/F ≤ δ(A+B) + 1/F` (using `Aseq_add_Bseq_subset` and
`0 ∈ Bseq A B n` to also get `Aseq A B n ⊆ A + B`). This is the density half
of `WEAK_KNESER_PLAN.md` step 2, ready to be combined (by whoever owns the
min-gap sequence) with an unboundedness or eventual-stabilization argument
on `F`. -/
theorem twoFoldLowerDensity_le_lowerDensity_add_add_inv_of_spacing
    {A B : Set ℕ} (hB0 : 0 ∈ B) {n F : ℕ} (hF : 0 < F)
    (hspace : ∀ x ∈ Bseq A B n, ∀ y ∈ Bseq A B n, x < y → F ≤ y - x) :
    twoFoldLowerDensity A B ≤ lowerDensity (A + B) + 1 / (F : ℝ) := by
  have h0Bn : 0 ∈ Bseq A B n := zero_mem_Bseq hB0 n
  have hbound := spacing_mul_posCount_le hF h0Bn hspace
  have hAsub : Aseq A B n ⊆ A + B := by
    have h1 : Aseq A B n ⊆ Aseq A B n + Bseq A B n := by
      intro a ha
      exact ⟨a, ha, 0, h0Bn, by simp⟩
    exact h1.trans (Aseq_add_Bseq_subset A B n)
  have hstep : twoFoldLowerDensity A B ≤ lowerDensity (Aseq A B n) + 1 / (F : ℝ) := by
    have heq : twoFoldLowerDensity A B = twoFoldLowerDensity (Aseq A B n) (Bseq A B n) :=
      (twoFoldLowerDensity_Aseq_Bseq A B n).symm
    rw [heq]
    unfold twoFoldLowerDensity lowerDensity
    -- pointwise bound: `(Aₙ(y)+Bₙ(y))/y ≤ Aₙ(y)/y + 1/F`
    have hptwise : ∀ y : ℕ, ((posCount (Aseq A B n) y : ℝ) + posCount (Bseq A B n) y) / y ≤
        (posCount (Aseq A B n) y : ℝ) / y + 1 / (F : ℝ) := by
      intro y
      rcases Nat.eq_zero_or_pos y with hy | hy
      · simp [hy]
      · rw [add_div]
        have hQy : (posCount (Bseq A B n) y : ℝ) / y ≤ 1 / (F : ℝ) := by
          have hb : (F : ℝ) * posCount (Bseq A B n) y ≤ y := by exact_mod_cast hbound y
          rw [div_le_div_iff₀ (by exact_mod_cast hy) (by exact_mod_cast hF)]
          nlinarith [hb]
        linarith [hQy]
    -- boundedness side conditions for the two `liminf`s being compared
    have hfbdd_ge : Filter.atTop.IsBoundedUnder (· ≥ ·)
        (fun y : ℕ => (posCount (Aseq A B n) y : ℝ) / y) :=
      isBoundedUnder_ge_div (fun y => by positivity)
    have hfbdd_le : Filter.atTop.IsBoundedUnder (· ≤ ·)
        (fun y : ℕ => (posCount (Aseq A B n) y : ℝ) / y) := by
      refine ⟨1, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun y => ?_)⟩
      rcases Nat.eq_zero_or_pos y with hy | hy
      · simp [hy]
      · rw [div_le_one (by exact_mod_cast hy)]
        exact_mod_cast posCount_le_self (Aseq A B n) y
    have hRbdd : Filter.atTop.IsBoundedUnder (· ≤ ·)
        (fun y : ℕ => (posCount (Aseq A B n) y : ℝ) / y + 1 / (F : ℝ)) := by
      obtain ⟨M, hM⟩ := hfbdd_le
      refine ⟨M + 1 / (F : ℝ), Filter.eventually_map.mpr ?_⟩
      filter_upwards [Filter.eventually_map.mp hM] with y hy
      linarith
    have hsumbdd_ge : Filter.atTop.IsBoundedUnder (· ≥ ·)
        (fun y : ℕ => ((posCount (Aseq A B n) y : ℝ) + posCount (Bseq A B n) y) / y) :=
      isBoundedUnder_ge_div (fun y => by positivity)
    have hle1 := Filter.liminf_le_liminf (Filter.Eventually.of_forall hptwise) hsumbdd_ge
      hRbdd.isCoboundedUnder_ge
    have hle2 := liminf_add_const Filter.atTop
      (fun y : ℕ => (posCount (Aseq A B n) y : ℝ) / y) (1 / (F : ℝ))
      hfbdd_le.isCoboundedUnder_ge hfbdd_ge
    rw [hle2] at hle1
    exact hle1
  calc twoFoldLowerDensity A B ≤ lowerDensity (Aseq A B n) + 1 / (F : ℝ) := hstep
    _ ≤ lowerDensity (A + B) + 1 / (F : ℝ) := by
        gcongr
        exact Erdos1112.Proof.Short.lowerDensity_mono hAsub

end Erdos1112.Proof.Short.KneserDensity
