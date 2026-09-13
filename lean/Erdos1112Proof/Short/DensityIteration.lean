/- The elementary iteration and growth-to-density bridge around the
*pending* Kneser density theorem.

This file does **not** discharge Kneser's theorem. The weak pairwise law
(`hkn` below) is an *explicit hypothesis* to every theorem that needs it —
never a hidden or declared `axiom` — and is documented as pending: the root
of the project is responsible for discharging it from Lane's published
dissertation proof (see `Short/KneserDensity/Defs.lean`'s header) or an
equivalent source. Nothing here closes that gap; it only builds the
*elementary* machinery around it:

1. `lowerDensity_range_ge_inv_of_growth`: a growth bound `P n ≤ c·n + C`
   (`c > 0`, `StrictMono P`) gives `1/c ≤ lowerDensity (Set.range P)` — the
   bridge from `Short/Density.count_bound_of_growth`'s `Finset`-count
   estimate (which counts `0` too, unlike `posCount`) to `lowerDensity`
   itself; the discrepancy is exactly the `+1`/`-1` noted in the task.
2. Standard bounds `0 ≤ lowerDensity A ≤ 1`, monotonicity under `⊆`, and the
   super-additivity `lowerDensity A + lowerDensity B ≤ twoFoldLowerDensity A B`
   (from Mathlib's generic `le_liminf_add`).
3. `HasAPTail`, and — *parameterized by* the pending law `hkn` — the
   induction `density_iterate`: for every `k`, either
   `k · lowerDensity (Set.range P) ≤ lowerDensity (kFoldSumset k P)` or
   `kFoldSumset k P` already has an AP tail.
4. `tailCovering_of_growth_lt`: combining (1)–(3), a growth bound with
   `c < k` cannot survive the density branch (it would force
   `lowerDensity (kFoldSumset k P) > 1`), so the AP-tail branch fires,
   giving `TailCovering k P` outright — again *conditional on* `hkn`. -/
import Mathlib
import Erdos1112Proof.Short.KneserDensity.Defs
import Erdos1112Proof.Short.Density
import Erdos1112Proof.Short.Kit

namespace Erdos1112.Proof.Short

open Erdos1112.Proof.Short.KneserDensity
open Erdos1112.Proof
open Filter
open scoped Classical Pointwise

/-! ### 1. Growth bound ⟹ `lowerDensity` lower bound -/

/-- The `Finset`-count from `count_bound_of_growth` counts `0` too (whenever
`0 ∈ Set.range p`, e.g. always here since it ranges over `Finset.range
(N+1) = [0,N]`), unlike `posCount`, which excludes it by convention. So the
`Finset`-count exceeds `posCount` by at most `1`. -/
lemma filterCard_le_posCount_succ (A : Set ℕ) (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun x => x ∈ A)).card ≤ posCount A N + 1 := by
  have hcoe : ((Finset.range (N + 1)).filter (fun x => x ∈ A) : Finset ℕ).card
      = ((Finset.range (N + 1)).filter (fun x => x ∈ A) : Set ℕ).ncard := by
    rw [Set.ncard_coe_finset]
  rw [hcoe]
  have hsub : ((Finset.range (N + 1)).filter (fun x => x ∈ A) : Set ℕ) ⊆
      ({0} : Set ℕ) ∪ (A ∩ Set.Icc 1 N) := by
    intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx
    rcases Nat.eq_zero_or_pos x with hx0 | hx0
    · left; exact hx0
    · right; exact ⟨hx.2, hx0, by omega⟩
  calc ((Finset.range (N + 1)).filter (fun x => x ∈ A) : Set ℕ).ncard
      ≤ (({0} : Set ℕ) ∪ (A ∩ Set.Icc 1 N)).ncard :=
        Set.ncard_le_ncard hsub
          (Set.finite_singleton 0 |>.union ((Set.finite_Icc 1 N).inter_of_right _))
    _ ≤ ({0} : Set ℕ).ncard + (A ∩ Set.Icc 1 N).ncard := Set.ncard_union_le _ _
    _ = posCount A N + 1 := by rw [Set.ncard_singleton]; unfold posCount; omega

/-- **Growth ⟹ `lowerDensity` lower bound.** If `P` is strictly monotone and
`P n ≤ c·n + C` eventually (`c > 0`), then `1/c ≤ lowerDensity (Set.range
P)`. This is the paper's `d̲(P) ≥ 1/c` step, built on
`Short.Density.count_bound_of_growth` (owned by the density-bridge file,
unmodified) with the `posCount`-vs-`Finset`-count `+1` correction. -/
theorem lowerDensity_range_ge_inv_of_growth {P : ℕ → ℕ} {c C : ℝ}
    (hmono : StrictMono P) (hc : 0 < c)
    (hbound : ∀ᶠ n in atTop, (P n : ℝ) ≤ c * n + C) :
    (1 / c) ≤ lowerDensity (Set.range P) := by
  have hcb := count_bound_of_growth hmono hc hbound
  set f : ℕ → ℝ := fun N => (posCount (Set.range P) N : ℝ) / N with hfdef
  set g : ℕ → ℝ := fun N => 1 / c - (C / c + 1) / N with hgdef
  have hev : g ≤ᶠ[atTop] f := by
    filter_upwards [hcb, eventually_gt_atTop 0] with N hN hNpos
    have hfc := filterCard_le_posCount_succ (Set.range P) N
    have hfc' : (((Finset.range (N + 1)).filter (fun x => x ∈ Set.range P)).card : ℝ) ≤
        (posCount (Set.range P) N : ℝ) + 1 := by exact_mod_cast hfc
    have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hkey : (N : ℝ) / c ≤ (posCount (Set.range P) N : ℝ) + C / c + 1 := by
      linarith [hN, hfc']
    show g N ≤ f N
    simp only [hgdef, hfdef]
    have hdiv : ((N : ℝ) / c) / N ≤ ((posCount (Set.range P) N : ℝ) + C / c + 1) / N := by
      gcongr
    rw [div_div, mul_comm c (N : ℝ), ← div_div, div_self hNR.ne'] at hdiv
    rw [add_div, add_div] at hdiv
    have e : (C / c + 1) / (N : ℝ) = C / c / N + 1 / N := add_div _ _ _
    linarith [hdiv, e]
  have hglim : Tendsto g atTop (nhds (1 / c)) := by
    have h1 : Tendsto (fun N : ℕ => (C / c + 1) / (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h2 := (tendsto_const_nhds (x := (1 : ℝ) / c)).sub h1
    simpa [hgdef] using h2
  have hbdd : IsBoundedUnder (· ≤ ·) atTop f := by
    rw [IsBoundedUnder, IsBounded]
    refine ⟨1, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with n
    simp only [hfdef]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · rw [div_le_one (by exact_mod_cast hn)]
      exact_mod_cast posCount_le_self (Set.range P) n
  have hle : liminf g atTop ≤ liminf f atTop :=
    Filter.liminf_le_liminf hev hglim.isBoundedUnder_ge hbdd.isCoboundedUnder_ge
  have hgliminf : liminf g atTop = 1 / c := hglim.liminf_eq
  rw [hgliminf] at hle
  exact hle

/-! ### 2. Standard `lowerDensity` bounds -/

lemma posCountDiv_isBoundedUnder_ge (A : Set ℕ) :
    IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ => (posCount A n : ℝ) / n) := by
  rw [IsBoundedUnder, IsBounded]
  refine ⟨0, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards with n
  positivity

lemma posCountDiv_isBoundedUnder_le (A : Set ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (posCount A n : ℝ) / n) := by
  rw [IsBoundedUnder, IsBounded]
  refine ⟨1, ?_⟩
  rw [Filter.eventually_map]
  filter_upwards with n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast posCount_le_self A n

/-- `0 ≤ δ(A)`. -/
theorem lowerDensity_nonneg (A : Set ℕ) : 0 ≤ lowerDensity A := by
  unfold lowerDensity
  apply le_liminf_of_le (posCountDiv_isBoundedUnder_le A).isCoboundedUnder_ge
  filter_upwards with n
  positivity

/-- `δ(A) ≤ 1`. -/
theorem lowerDensity_le_one (A : Set ℕ) : lowerDensity A ≤ 1 := by
  unfold lowerDensity
  apply liminf_le_of_le (posCountDiv_isBoundedUnder_ge A)
  intro b hb
  obtain ⟨N, hbN, hN1⟩ := (hb.and (eventually_gt_atTop 0)).exists
  have h1 : (posCount A N : ℝ) / N ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hN1)]
    exact_mod_cast posCount_le_self A N
  linarith [hbN, h1]

/-- `δ` is monotone under `⊆`. -/
theorem lowerDensity_mono {A B : Set ℕ} (h : A ⊆ B) : lowerDensity A ≤ lowerDensity B := by
  unfold lowerDensity
  apply Filter.liminf_le_liminf
  · filter_upwards with n; gcongr; exact posCount_mono h n
  · exact posCountDiv_isBoundedUnder_ge A
  · exact (posCountDiv_isBoundedUnder_le B).isCoboundedUnder_ge

/-- `δ(A) + δ(B) ≤ δ(A,B)`, the standard super-additivity of `liminf` under
addition (Mathlib's `le_liminf_add`), specialized to `posCount`-quotients
(both bounded in `[0,1]`, so all the `IsBoundedUnder`/`IsCoboundedUnder`
side conditions are the elementary facts above). -/
theorem add_lowerDensity_le_twoFoldLowerDensity (A B : Set ℕ) :
    lowerDensity A + lowerDensity B ≤ twoFoldLowerDensity A B := by
  unfold lowerDensity twoFoldLowerDensity
  have key := le_liminf_add (f := atTop) (u := fun n : ℕ => (posCount A n : ℝ) / n)
    (v := fun n : ℕ => (posCount B n : ℝ) / n)
    (posCountDiv_isBoundedUnder_ge A) (posCountDiv_isBoundedUnder_le A)
    (posCountDiv_isBoundedUnder_ge B) (posCountDiv_isBoundedUnder_le B).isCoboundedUnder_ge
  have heq : (fun n : ℕ => (posCount A n : ℝ) / n) + (fun n : ℕ => (posCount B n : ℝ) / n)
      = fun n : ℕ => ((posCount A n : ℝ) + posCount B n) / n := by
    funext n; simp [add_div]
  rwa [heq] at key

/-! ### 3. `HasAPTail` and the density/AP-tail iteration

**Important**: `density_iterate` and everything after it take the weak
pairwise Kneser law `hkn` as an *explicit hypothesis*. This is Lane's
dissertation result (a genuine, published, nontrivial density theorem); it
is *not* proved in this file, and no `axiom` declaration is used to smuggle
it in. Every theorem that needs it lists it as a named argument, so the
dependency is visible at every call site and in every signature. Whoever
finishes the Kneser development (the root, per this task's instructions)
supplies a proof term for `hkn`; nothing here can be used to close the
Erdős 1112 proof without that term. -/

/-- `S` contains a full arithmetic-progression tail: `x + q·j ∈ S` for every
`j ≥ 0`, some `q > 0`. -/
def HasAPTail (S : Set ℕ) : Prop := ∃ q : ℕ, 0 < q ∧ ∃ x : ℕ, ∀ j, x + q * j ∈ S

/-- `HasAPTail` propagates to any superset. -/
theorem HasAPTail.mono {S T : Set ℕ} (h : S ⊆ T) (hS : HasAPTail S) : HasAPTail T := by
  obtain ⟨q, hq, x, hx⟩ := hS
  exact ⟨q, hq, x, fun j => h (hx j)⟩

/-- An AP tail of the `k`-fold sumset gives `TailCovering` directly (the
same construction as `Kit.tailCoveringN_of_AP`, generalized from a base
point of the special form `k·c` to an arbitrary base point `x`, which is
what `HasAPTail`'s witness supplies). -/
theorem tailCovering_of_hasAPTail {k : ℕ} {P : ℕ → ℕ} (h : HasAPTail (kFoldSumset k P)) :
    TailCovering k P := by
  obtain ⟨q, hq, x, hx⟩ := h
  refine ⟨q, hq, x % q, Nat.mod_lt _ hq, x, fun y hy hymod => ?_⟩
  have hdvd : q ∣ y - x := (Nat.modEq_iff_dvd' hy).mp hymod.symm
  obtain ⟨j, hj⟩ := hdvd
  have hyeq : y = x + q * j := by omega
  rw [hyeq]; exact hx j

/-- **Density/AP-tail iteration** (conditional on `hkn`, see above). For
`P` with `P 0 = 0`, at every fold count `k`, either the density has grown
by the expected factor `k`, or the `k`-fold sumset already has an AP tail.
Induction on `k`: the base case `k = 0` is `lowerDensity_nonneg`; the step
applies `hkn` to `(kFoldSumset k P, Set.range P)` (both contain `0`, since
`P 0 = 0` and any constant configuration sums to `0`) and transports either
alternative forward along `kFoldSumset k P + Set.range P ⊆ kFoldSumset
(k+1) P` (`Kit.add_mem_kFoldSumset`, `k`-copies plus one more term). -/
theorem density_iterate (hkn : ∀ A B : Set ℕ, 0 ∈ A → 0 ∈ B →
      lowerDensity A + lowerDensity B ≤ lowerDensity (A + B) ∨ HasAPTail (A + B))
    {P : ℕ → ℕ} (hP0 : P 0 = 0) :
    ∀ k : ℕ, (k : ℝ) * lowerDensity (Set.range P) ≤ lowerDensity (kFoldSumset k P) ∨
      HasAPTail (kFoldSumset k P) := by
  have hone : (0 : ℕ) ∈ kFoldSumset 1 P := ⟨fun _ => 0, by simp [hP0]⟩
  have hsub1 : ∀ k : ℕ, kFoldSumset k P + Set.range P ⊆ kFoldSumset (k + 1) P := by
    intro k
    rintro _ ⟨u, hu, v, hv, rfl⟩
    have h1 : v ∈ kFoldSumset 1 P := by
      obtain ⟨m, rfl⟩ := hv
      exact single_mem_kFoldSumset m
    have := add_mem_kFoldSumset hu h1
    simpa using this
  have hsub2 : ∀ k : ℕ, kFoldSumset k P ⊆ kFoldSumset (k + 1) P := by
    intro k y hy
    have := add_mem_kFoldSumset hy hone
    simpa using this
  intro k
  induction k with
  | zero =>
      left
      simp only [Nat.cast_zero, zero_mul]
      exact lowerDensity_nonneg _
  | succ k ih =>
      rcases ih with ihL | ihR
      · have h0k : (0 : ℕ) ∈ kFoldSumset k P := ⟨fun _ => 0, by simp [hP0]⟩
        have h0P : (0 : ℕ) ∈ Set.range P := ⟨0, hP0⟩
        rcases hkn (kFoldSumset k P) (Set.range P) h0k h0P with hd | hap
        · left
          have hmono := lowerDensity_mono (hsub1 k)
          have hcast : ((k : ℝ) + 1) * lowerDensity (Set.range P) =
              (k : ℝ) * lowerDensity (Set.range P) + lowerDensity (Set.range P) := by ring
          push_cast
          rw [hcast]
          calc (k : ℝ) * lowerDensity (Set.range P) + lowerDensity (Set.range P)
              ≤ lowerDensity (kFoldSumset k P) + lowerDensity (Set.range P) := by linarith [ihL]
            _ ≤ lowerDensity (kFoldSumset k P + Set.range P) := hd
            _ ≤ lowerDensity (kFoldSumset (k + 1) P) := hmono
        · right; exact hap.mono (hsub1 k)
      · right; exact ihR.mono (hsub2 k)

/-! ### 4. Assembly: a growth bound with `c < k` forces `TailCovering` -/

/-- **The growth-to-covering bridge (conditional on `hkn`).** If `P 0 = 0`,
`P` is strictly monotone, and `P n ≤ c·n + C` eventually with `0 < c < k`,
then `P` is `k`-tail-covering. Proof: the growth bound forces
`lowerDensity (Set.range P) ≥ 1/c`; if `density_iterate`'s density branch
held at this `k`, it would force `lowerDensity (kFoldSumset k P) ≥ k/c > 1`,
contradicting `lowerDensity_le_one`. So the AP-tail branch must hold, and
`tailCovering_of_hasAPTail` finishes. This is exactly the paper's "density
shortcut": `p_n ≤ cn + C` with `c < k` gives a congruence-class tail in
`kP` — **conditional on `hkn`**, the pending weak pairwise Kneser law. -/
theorem tailCovering_of_growth_lt
    (hkn : ∀ A B : Set ℕ, 0 ∈ A → 0 ∈ B →
      lowerDensity A + lowerDensity B ≤ lowerDensity (A + B) ∨ HasAPTail (A + B))
    {k : ℕ} {P : ℕ → ℕ} {c C : ℝ} (hP0 : P 0 = 0) (hmono : StrictMono P)
    (hc : 0 < c) (hck : c < (k : ℝ))
    (hbound : ∀ᶠ n in atTop, (P n : ℝ) ≤ c * n + C) :
    TailCovering k P := by
  have hden := lowerDensity_range_ge_inv_of_growth hmono hc hbound
  have hle1 := lowerDensity_le_one (kFoldSumset k P)
  rcases density_iterate hkn hP0 k with hL | hR
  · exfalso
    have hkdc : (k : ℝ) / c ≤ (k : ℝ) * lowerDensity (Set.range P) := by
      rw [div_le_iff₀ hc]
      have h1 : (1 : ℝ) ≤ lowerDensity (Set.range P) * c := by
        rw [← div_le_iff₀ hc] at *; linarith [hden]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [h1, hk0]
    have hgt1 : (1 : ℝ) < (k : ℝ) / c := by rw [lt_div_iff₀ hc]; linarith [hck]
    linarith [hL, hle1, hkdc, hgt1]
  · exact tailCovering_of_hasAPTail hR

end Erdos1112.Proof.Short
