/- A fair sequence of e-transformations.

The transformation operation is a parameter with explicit elementary laws.
Both an ordinary e-transform and its maximal version have this shape. The
concrete operation and its density invariance are separate dependencies.
-/
import Erdos1112Proof.Short.DensityLimit

namespace Erdos1112.Proof.Short.KneserDensity

open scoped Pointwise Classical

abbrev PairState := Set ℕ × Set ℕ

def Unresolved (s : PairState) (e : ℕ) : Prop :=
  e ∈ s.1 ∧ ∃ b ∈ s.2, e + b ∉ s.1

noncomputable def leastUnresolved (s : PairState) : ℕ :=
  if h : ∃ e, Unresolved s e then Nat.find h else 0

lemma leastUnresolved_spec {s : PairState} (h : ∃ e, Unresolved s e) :
    Unresolved s (leastUnresolved s) := by
  classical
  simpa [leastUnresolved, h] using Nat.find_spec h

lemma leastUnresolved_le {s : PairState} {a : ℕ} (ha : Unresolved s a) :
    leastUnresolved s ≤ a := by
  classical
  have h : ∃ e, Unresolved s e := ⟨a, ha⟩
  simpa [leastUnresolved, h] using Nat.find_min' h ha

noncomputable def transformNext (step : PairState → ℕ → PairState) (s : PairState) : PairState :=
  if ∃ e, Unresolved s e then step s (leastUnresolved s) else s

noncomputable def transformSequence (step : PairState → ℕ → PairState) (s : PairState) :
    ℕ → PairState
  | 0 => s
  | n + 1 => transformNext step (transformSequence step s n)

/-- The elementary order and absorption properties of an active transform. -/
structure TransformLaws (step : PairState → ℕ → PairState) : Prop where
  left : ∀ s e, Unresolved s e → s.1 ⊆ (step s e).1
  right : ∀ s e, Unresolved s e → (step s e).2 ⊆ s.2
  absorbs : ∀ s e, Unresolved s e → ∀ b ∈ (step s e).2, e + b ∈ (step s e).1

lemma next_left {step : PairState → ℕ → PairState} (hlaw : TransformLaws step) (s : PairState) :
    s.1 ⊆ (transformNext step s).1 := by
  classical
  by_cases h : ∃ e, Unresolved s e
  · simpa [transformNext, h] using hlaw.left s _ (leastUnresolved_spec h)
  · simp [transformNext, h]

lemma next_right {step : PairState → ℕ → PairState} (hlaw : TransformLaws step) (s : PairState) :
    (transformNext step s).2 ⊆ s.2 := by
  classical
  by_cases h : ∃ e, Unresolved s e
  · simpa [transformNext, h] using hlaw.right s _ (leastUnresolved_spec h)
  · simp [transformNext, h]

lemma sequence_left_mono {step : PairState → ℕ → PairState} (hlaw : TransformLaws step)
    (s : PairState) : Monotone (fun n => (transformSequence step s n).1) := by
  apply monotone_nat_of_le_succ
  intro n
  exact next_left hlaw _

lemma sequence_right_anti {step : PairState → ℕ → PairState} (hlaw : TransformLaws step)
    (s : PairState) : Antitone (fun n => (transformSequence step s n).2) := by
  apply antitone_nat_of_succ_le
  intro n
  exact next_right hlaw _

/-- The least-unresolved-element process satisfies the fairness used by
`DensityLimit`: each first-component element eventually absorbs the tail. -/
theorem transformSequence_fair {step : PairState → ℕ → PairState} (hlaw : TransformLaws step)
    (s : PairState) : FairAbsorption (fun n => (transformSequence step s n).1)
      (fun n => (transformSequence step s n).2) := by
  classical
  apply fair_of_least_choices (e := fun n => leastUnresolved (transformSequence step s n))
    (sequence_left_mono hlaw s) (sequence_right_anti hlaw s)
  · intro i a ha hb
    have hu : Unresolved (transformSequence step s i) a := ⟨ha, hb⟩
    exact ⟨leastUnresolved_le hu, (leastUnresolved_spec ⟨a, hu⟩).2⟩
  · intro i hi b hb
    have hh : ∃ e, Unresolved (transformSequence step s i) e := hi
    have hb' : b ∈ (step (transformSequence step s i)
        (leastUnresolved (transformSequence step s i))).2 := by
      simpa [transformSequence, transformNext, hh] using hb
    simpa [transformSequence, transformNext, hh] using
      hlaw.absorbs _ _ (leastUnresolved_spec hh) b hb'

/-- Any quantity nondecreasing under active transforms stays above its
initial value. Applied later to the joint lower density. -/
theorem transformSequence_score {step : PairState → ℕ → PairState} {φ : PairState → ℝ}
    (hφ : ∀ s e, Unresolved s e → φ s ≤ φ (step s e)) (s : PairState) :
    ∀ n, φ s ≤ φ (transformSequence step s n) := by
  classical
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    by_cases h : ∃ e, Unresolved (transformSequence step s n) e
    · simpa [transformSequence, transformNext, h] using
        ih.trans (hφ _ _ (leastUnresolved_spec h))
    · simpa [transformSequence, transformNext, h] using ih

/-- Containment of the original sumset persists through the whole sequence. -/
theorem transformSequence_sum_subset {step : PairState → ℕ → PairState}
    (hstep : ∀ s e, Unresolved s e → (step s e).1 + (step s e).2 ⊆ s.1 + s.2)
    (s : PairState) : ∀ n,
      (transformSequence step s n).1 + (transformSequence step s n).2 ⊆ s.1 + s.2 := by
  classical
  intro n
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
    by_cases h : ∃ e, Unresolved (transformSequence step s n) e
    · simpa [transformSequence, transformNext, h] using
        (hstep _ _ (leastUnresolved_spec h)).trans ih
    · simpa [transformSequence, transformNext, h] using ih

end Erdos1112.Proof.Short.KneserDensity
