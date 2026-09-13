/- The limit-set step in the Kneser density argument.

For an increasing first component and decreasing second component of a fair
sequence of transformations, any surviving positive element generates an
arithmetic progression in the original sumset. Only this consequence of the
nonzero-limit case is needed for tail covering; no global periodicity claim
is made here. Fairness must still be supplied by the transformation sequence.
-/
import Mathlib

namespace Erdos1112.Proof.Short.KneserDensity

/-- Each element eventually absorbs the remaining second component. -/
def FairAbsorption (A B : ℕ → Set ℕ) : Prop :=
  ∀ i a, a ∈ A i → ∃ j, i ≤ j ∧ ∀ b ∈ B j, a + b ∈ A j

/-- Choosing a least unresolved element at each active step is fair: a
fixed unresolved element would bound infinitely many distinct earlier choices.
The hypotheses state the elementary properties supplied by an e-transform. -/
theorem fair_of_least_choices {A B : ℕ → Set ℕ} {e : ℕ → ℕ}
    (hmono : Monotone A) (hanti : Antitone B)
    (hchoose : ∀ i a, a ∈ A i → (∃ b ∈ B i, a + b ∉ A i) →
      e i ≤ a ∧ ∃ b ∈ B i, e i + b ∉ A i)
    (hresolve : ∀ i, (∃ a ∈ A i, ∃ b ∈ B i, a + b ∉ A i) →
      ∀ b ∈ B (i + 1), e i + b ∈ A (i + 1)) :
    FairAbsorption A B := by
  classical
  intro i a ha
  by_contra hfail
  push_neg at hfail
  have hbad (j : ℕ) (hj : i ≤ j) : ∃ b ∈ B j, a + b ∉ A j := hfail j hj
  have hsel (n : ℕ) : e (i + n) ≤ a ∧ ∃ b ∈ B (i + n), e (i + n) + b ∉ A (i + n) :=
    hchoose (i + n) a (hmono (by omega) ha) (hbad (i + n) (by omega))
  have hdistinct {m n : ℕ} (hmn : m < n) : e (i + m) ≠ e (i + n) := by
    intro heq
    obtain ⟨b, hb, hnb⟩ := (hsel n).2
    have hresolved := hresolve (i + m)
      ⟨a, hmono (by omega) ha, hbad (i + m) (by omega)⟩ b
      (hanti (show i + m + 1 ≤ i + n by omega) hb)
    rw [heq] at hresolved
    exact hnb (hmono (show i + m + 1 ≤ i + n by omega) hresolved)
  have hinj : Function.Injective (fun n => e (i + n)) := by
    intro m n heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hdistinct hlt heq
    · exact hdistinct hgt heq.symm
  have hfinite : (Set.range (fun n => e (i + n))).Finite :=
    (Set.finite_Iic a).subset (by
      rintro _ ⟨n, rfl⟩
      exact (hsel n).1)
  exact Set.infinite_range_of_injective hinj hfinite

/-- Fairness simultaneously absorbs any finite set of first-component
values. Monotonicity makes previously satisfied requirements persist. -/
theorem finite_absorption {A B : ℕ → Set ℕ} (hfair : FairAbsorption A B)
    (hmono : Monotone A) (hanti : Antitone B) (i : ℕ) (E : Finset ℕ)
    (hE : ∀ e ∈ E, e ∈ A i) :
    ∃ j ≥ i, ∀ e ∈ E, ∀ b ∈ B j, e + b ∈ A j := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨i, le_rfl, by simp⟩
  | @insert e E he ih =>
    obtain ⟨j, hji, hj⟩ := ih (fun a ha => hE a (Finset.mem_insert_of_mem ha))
    obtain ⟨l, hli, hl⟩ := hfair i e (hE e (Finset.mem_insert_self _ _))
    refine ⟨max j l, hji.trans (le_max_left _ _), ?_⟩
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hmono (le_max_right j l) (hl b (hanti (le_max_right j l) hb))
    · exact hmono (le_max_left j l) (hj a ha b (hanti (le_max_left j l) hb))

/-- If every second component contains a pair at a fixed distance, fair
absorption grows first-component progressions at that distance to arbitrary
finite length. This is the elementary block-growth step of the density proof. -/
theorem arbitrary_progressions_of_pairs {A B : ℕ → Set ℕ} {f : ℕ}
    (hfair : FairAbsorption A B) (hmono : Monotone A) (hanti : Antitone B)
    (hA : (A 0).Nonempty) (hpairs : ∀ n, ∃ b ∈ B n, b + f ∈ B n) :
    ∀ m, ∃ n x, ∀ j ≤ m, x + f * j ∈ A n := by
  classical
  intro m
  induction m with
  | zero =>
    obtain ⟨x, hx⟩ := hA
    refine ⟨0, x, fun j hj => ?_⟩
    have hj0 : j = 0 := by omega
    simpa [hj0] using hx
  | succ m ih =>
    obtain ⟨n, x, hx⟩ := ih
    let E := (Finset.range (m + 1)).image (fun j => x + f * j)
    have hE : ∀ e ∈ E, e ∈ A n := by
      intro e he
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
      exact hx j (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)
    obtain ⟨l, _, hl⟩ := finite_absorption hfair hmono hanti n E hE
    obtain ⟨b, hb, hbf⟩ := hpairs l
    refine ⟨l, x + b, fun j hj => ?_⟩
    by_cases hjm : j ≤ m
    · have hmem : x + f * j ∈ E := Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
      have hh := hl _ hmem b hb
      convert hh using 1
      ring
    · have heq : j = m + 1 := by omega
      have hmem : x + f * m ∈ E := Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (by omega), rfl⟩
      have hh := hl _ hmem (b + f) hbf
      rw [heq]
      convert hh using 1
      ring

/-- Fair absorption passes to the union/intersection limits. -/
theorem fair_limit_absorbs {A B : ℕ → Set ℕ} (hfair : FairAbsorption A B)
    {a b : ℕ} (ha : a ∈ ⋃ i, A i) (hb : b ∈ ⋂ i, B i) :
    a + b ∈ ⋃ i, A i := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, _, hj⟩ := hfair i a hi
  exact Set.mem_iUnion.mpr ⟨j, hj b (Set.mem_iInter.mp hb j)⟩

/-- A surviving positive element supplies a full progression from any point
of the first limit set. This is the needed nonzero-limit alternative. -/
theorem progression_of_limit {A B : ℕ → Set ℕ} {C : Set ℕ}
    (hfair : FairAbsorption A B) (hsub : ∀ i, A i ⊆ C)
    {x q : ℕ} (hx : x ∈ ⋃ i, A i) (hq : q ∈ ⋂ i, B i) :
    ∀ j, x + q * j ∈ C := by
  have hmem : ∀ j, x + q * j ∈ ⋃ i, A i := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      have hh := fair_limit_absorbs hfair ih hq
      simpa only [Nat.mul_succ, Nat.add_assoc] using hh
  intro j
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hmem j)
  exact hsub i hi

/-- If the ambient sumset contains no progression tail, every survivor in
the second limit set is zero. -/
theorem limit_eq_zero_of_no_progression {A B : ℕ → Set ℕ} {C : Set ℕ}
    (hfair : FairAbsorption A B) (hsub : ∀ i, A i ⊆ C)
    (hA : (⋃ i, A i).Nonempty)
    (hno : ¬ ∃ q > 0, ∃ x, ∀ j, x + q * j ∈ C) :
    ∀ b ∈ ⋂ i, B i, b = 0 := by
  intro b hb
  by_contra hne
  obtain ⟨x, hx⟩ := hA
  exact hno ⟨b, Nat.pos_of_ne_zero hne, x, progression_of_limit hfair hsub hx hb⟩

/-- For a decreasing sequence with no positive survivor, every fixed finite
prefix is eventually emptied of positive elements. -/
theorem finite_prefix_eventually_deleted {B : ℕ → Set ℕ} (hanti : Antitone B)
    (hlim : ∀ b ∈ ⋂ i, B i, b = 0) :
    ∀ N, ∃ i, ∀ b ∈ B i, b ≤ N → b = 0 := by
  classical
  intro N
  induction N with
  | zero => exact ⟨0, fun b _ hb => Nat.eq_zero_of_le_zero hb⟩
  | succ N ih =>
    obtain ⟨i, hi⟩ := ih
    have hn : ¬ N + 1 ∈ ⋂ j, B j := by
      intro hh
      have := hlim (N + 1) hh
      omega
    simp only [Set.mem_iInter] at hn
    push_neg at hn
    obtain ⟨j, hj⟩ := hn
    refine ⟨max i j, fun b hb hNb => ?_⟩
    by_cases hbeq : b = N + 1
    · subst b
      exact False.elim (hj (hanti (le_max_right i j) hb))
    · exact hi b (hanti (le_max_left i j) hb) (by omega)

end Erdos1112.Proof.Short.KneserDensity
