/-
Finite modular subset-sum covering, for the Kneser weak-density proof.

Given a finite alphabet `G : Finset ℕ` and a modulus `F > 0` with
`gcd (insert F G) = 1`, this produces a single finite multiset `S` with all
entries in `G` whose subset sums hit *every* residue mod `F`. Built from
Bézout's identity for a finite set (elementary finite cyclic group
generation: `ZMod F` is a finite additive group, so a generating set's
additive submonoid is already the whole group) plus a stacking trick to turn
one representative of residue `1` into representatives of every residue.

Independent of the old `Sharp.Main`/tables/staircase and of the new `SHARP`
lemma: this file imports only `Erdos1112Proof.SubsetSums` (the multiset
subset-sum API) and core Mathlib (`Nat.gcd_eq_gcd_ab`, `Finset.gcd`, `ZMod`).
-/
import Erdos1112Proof.SubsetSums

namespace Erdos1112.Proof.Short

open Finset

/-! ### Bézout's identity for a finite set

For any finite set of naturals, some integer combination of its elements
equals its gcd (vacuously, for the empty set, since `∅.gcd id = 0` and the
empty sum is `0`). No coprimality hypothesis is needed here: it is folded
into the value of the gcd on the right. -/

theorem bezout_sum (s : Finset ℕ) :
    ∃ c : ℕ → ℤ, ∑ x ∈ s, c x * (x : ℤ) = ((s.gcd (id : ℕ → ℕ) : ℕ) : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a t hat ih =>
    obtain ⟨c, hc⟩ := ih
    have hgcd : (insert a t).gcd id = Nat.gcd a (t.gcd id) := Finset.gcd_insert
    have hbezout : (Nat.gcd a (t.gcd id) : ℤ) =
        a * Nat.gcdA a (t.gcd id) + ((t.gcd id : ℕ) : ℤ) * Nat.gcdB a (t.gcd id) :=
      Nat.gcd_eq_gcd_ab a (t.gcd id)
    refine ⟨fun y => if y = a then Nat.gcdA a (t.gcd id) else c y * Nat.gcdB a (t.gcd id), ?_⟩
    rw [Finset.sum_insert hat]
    dsimp only
    rw [if_pos rfl]
    have step : ∑ y ∈ t, (if y = a then Nat.gcdA a (t.gcd id) else c y * Nat.gcdB a (t.gcd id)) *
          (y : ℤ) = Nat.gcdB a (t.gcd id) * ∑ y ∈ t, c y * (y : ℤ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [if_neg (fun h : y = a => hat (h ▸ hy))]
      ring
    rw [step, hc, hgcd, hbezout]
    ring

/-! ### Stacking a multiset `t` times -/

/-- `stack M n` is `M` concatenated with itself `n` times. -/
def stack (M : Multiset ℕ) : ℕ → Multiset ℕ
  | 0 => 0
  | n + 1 => M + stack M n

@[simp] lemma stack_zero (M : Multiset ℕ) : stack M 0 = 0 := rfl

lemma stack_succ (M : Multiset ℕ) (n : ℕ) : stack M (n + 1) = M + stack M n := rfl

lemma stack_sum (M : Multiset ℕ) : ∀ n, (stack M n).sum = n * M.sum
  | 0 => by simp
  | n + 1 => by rw [stack_succ, Multiset.sum_add, stack_sum M n]; ring

lemma stack_mono (M : Multiset ℕ) : ∀ {m n}, m ≤ n → stack M m ≤ stack M n
  | m, n, h => by
    obtain ⟨k, rfl⟩ := Nat.le.dest h
    clear h
    induction k with
    | zero => exact le_refl _
    | succ k ih =>
      have he : m + (k + 1) = (m + k) + 1 := by ring
      rw [he, stack_succ]
      exact ih.trans (le_add_self)

lemma stack_subset {M : Multiset ℕ} {G : Finset ℕ} (hM : ∀ x ∈ M, x ∈ G) :
    ∀ n x, x ∈ stack M n → x ∈ G
  | 0, x, hx => by simp at hx
  | n + 1, x, hx => by
      rw [stack_succ, Multiset.mem_add] at hx
      rcases hx with hx | hx
      · exact hM x hx
      · exact stack_subset hM n x hx

/-! ### Sum of a Finset-indexed family of replicate multisets -/

lemma sum_replicate_sum (G : Finset ℕ) (c : ℕ → ℕ) :
    (∑ x ∈ G, Multiset.replicate (c x) x).sum = ∑ x ∈ G, c x * x := by
  classical
  induction G using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.sum_insert hat, Finset.sum_insert hat, Multiset.sum_add, ih,
      Multiset.sum_replicate, smul_eq_mul]

lemma mem_sum_replicate {G : Finset ℕ} {c : ℕ → ℕ} {x : ℕ}
    (hx : x ∈ ∑ y ∈ G, Multiset.replicate (c y) y) : x ∈ G := by
  classical
  induction G using Finset.induction_on with
  | empty => simp at hx
  | insert a t hat ih =>
    rw [Finset.sum_insert hat, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · rw [Multiset.eq_of_mem_replicate hx]; exact Finset.mem_insert_self a t
    · exact Finset.mem_insert_of_mem (ih hx)

/-! ### The covering theorem -/

/-- **Finite modular subset-sum covering.** If `gcd (insert F G) = 1`, there
is a finite multiset `S` with every entry in `G` whose subset sums realize
every residue mod `F`. No bound on `S.card` is claimed or needed. -/
theorem exists_modular_cover (G : Finset ℕ) (F : ℕ) (hF : 0 < F)
    (hgcd : (insert F G).gcd id = 1) :
    ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ G) ∧ ∀ r < F, ∃ u ∈ subsetSums S, u % F = r := by
  classical
  haveI : NeZero F := ⟨hF.ne'⟩
  obtain ⟨c, hc⟩ := bezout_sum (insert F G)
  rw [hgcd] at hc
  -- Cast the Bézout identity to `ZMod F`; the `F` term vanishes there, and
  -- what remains is an equation over `G` alone.
  have hcast : ((∑ x ∈ insert F G, c x * (x : ℤ) : ℤ) : ZMod F) = ((1 : ℤ) : ZMod F) :=
    congrArg (fun z : ℤ => (z : ZMod F)) hc
  rw [Int.cast_one] at hcast
  push_cast at hcast
  have hzero : (c F : ZMod F) * (F : ZMod F) = 0 := by rw [ZMod.natCast_self]; ring
  have hstep : (∑ x ∈ insert F G, (c x : ZMod F) * (x : ZMod F)) =
      ∑ x ∈ G, (c x : ZMod F) * (x : ZMod F) := Finset.sum_insert_zero hzero
  rw [hstep] at hcast
  -- Reduce each integer coefficient mod `F` to a natural number without
  -- changing its class mod `F`.
  set c' : ℕ → ℕ := fun x => (c x % (F : ℤ)).toNat with hc'_def
  have hc'cast : ∀ x, ((c' x : ℕ) : ZMod F) = (c x : ZMod F) := by
    intro x
    have hnn : (0 : ℤ) ≤ c x % (F : ℤ) := Int.emod_nonneg (c x) (by exact_mod_cast hF.ne')
    have : ((c' x : ℕ) : ℤ) = c x % (F : ℤ) := by
      rw [hc'_def]; exact Int.toNat_of_nonneg hnn
    calc ((c' x : ℕ) : ZMod F) = (((c' x : ℕ) : ℤ) : ZMod F) := by push_cast; ring
      _ = ((c x % (F : ℤ) : ℤ) : ZMod F) := by rw [this]
      _ = (c x : ZMod F) := ZMod.intCast_mod (c x) F
  have hnat : ((∑ x ∈ G, c' x * x : ℕ) : ZMod F) = 1 := by
    push_cast
    rw [Finset.sum_congr rfl (fun x _ => by rw [hc'cast x])]
    exact hcast
  have hmodeq : (∑ x ∈ G, c' x * x) % F = 1 % F := (ZMod.natCast_eq_natCast_iff _ _ _).mp
    (by rw [hnat]; push_cast; ring_nf)
  -- Package the coefficients into an actual multiset, one representative
  -- of residue `1`, then stack it `F - 1` times to reach every residue.
  set S₁ : Multiset ℕ := ∑ x ∈ G, Multiset.replicate (c' x) x with hS₁_def
  have hS₁_sum : S₁.sum = ∑ x ∈ G, c' x * x := sum_replicate_sum G c'
  have hS₁_mem : ∀ x ∈ S₁, x ∈ G := fun x hx => mem_sum_replicate hx
  refine ⟨stack S₁ (F - 1), stack_subset hS₁_mem (F - 1), fun r hr => ?_⟩
  refine ⟨(stack S₁ r).sum, mem_subsetSums.mpr ⟨stack S₁ r, stack_mono S₁ (by omega), rfl⟩, ?_⟩
  rw [stack_sum]
  have hcong : r * S₁.sum ≡ r * 1 [MOD F] := Nat.ModEq.mul_left r (by rw [hS₁_sum]; exact hmodeq)
  have : r * S₁.sum % F = r * 1 % F := hcong
  rw [this, mul_one, Nat.mod_eq_of_lt hr]

/-! ### Bonus: the residue alphabet of an antitone family stabilizes

Not needed for `exists_modular_cover` above, but requested if feasible: for a
`⊆`-decreasing family `B : ℕ → Set ℕ`, the finite set of residues mod `F`
realized by `B n` is eventually constant. This is what lets the caller fix a
single stable alphabet `R` to feed into `exists_modular_cover`. -/

open Classical in
/-- The residues mod `F` realized by `B n`. -/
noncomputable def resSet (B : ℕ → Set ℕ) (F n : ℕ) : Finset ℕ :=
  (Finset.range F).filter (fun r => ∃ b ∈ B n, b % F = r)

lemma mem_resSet {B : ℕ → Set ℕ} {F n r : ℕ} :
    r ∈ resSet B F n ↔ r < F ∧ ∃ b ∈ B n, b % F = r := by
  classical
  simp [resSet, Finset.mem_filter, Finset.mem_range]

lemma resSet_succ_subset {B : ℕ → Set ℕ} (hanti : ∀ n, B (n + 1) ⊆ B n) (F n : ℕ) :
    resSet B F (n + 1) ⊆ resSet B F n := by
  intro r hr
  rw [mem_resSet] at hr ⊢
  obtain ⟨hrF, b, hb, hbr⟩ := hr
  exact ⟨hrF, b, hanti n hb, hbr⟩

/-- A nonincreasing sequence of naturals is eventually constant. -/
theorem exists_eventually_const {f : ℕ → ℕ} (hf : Antitone f) :
    ∃ N, ∀ n ≥ N, f n = f N := by
  obtain ⟨N, hN⟩ := Nat.sInf_mem (Set.range_nonempty f)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : f n ≤ f N := hf hn
  have h2 : sInf (Set.range f) ≤ f n := Nat.sInf_le ⟨n, rfl⟩
  omega

/-- **The residue alphabet of a decreasing family stabilizes.** For
`B : ℕ → Set ℕ` with `B (n+1) ⊆ B n`, the residues mod `F` realized by `B n`
are eventually constant in `n`. -/
theorem exists_stable_residues (B : ℕ → Set ℕ) (F : ℕ) (hanti : ∀ n, B (n + 1) ⊆ B n) :
    ∃ N, ∀ n ≥ N, resSet B F n = resSet B F N := by
  have hSetAnti : Antitone (resSet B F) := antitone_nat_of_succ_le (resSet_succ_subset hanti F)
  have hCardAnti : Antitone (fun n => (resSet B F n).card) :=
    fun _ _ hmn => Finset.card_le_card (hSetAnti hmn)
  obtain ⟨N, hN⟩ := exists_eventually_const hCardAnti
  refine ⟨N, fun n hn => ?_⟩
  exact Finset.eq_of_subset_of_card_le (hSetAnti hn) (le_of_eq (hN n hn).symm)

end Erdos1112.Proof.Short
