/-
Case B support: completeness of the Table-B class table.

A Case-B target `(a, b, M)` (hard core, `a ∤ M`, `a ∤ b+M`, `e ≠ h`,
`a ≤ 11`, `μ = M−a ≥ 12`) determines the data `(a, h, b)` with `h := M − b`;
its class is `(a, b % a, h)`. `caseBGuard` records exactly the conditions on
`(a, h, b)` that follow from the Case-B hypotheses. The decided sweep
`caseBComplete` checks, for every guard-passing `(a, h, b)` with `b ≤ 53`,
that some row of `certTableB` is a λ-chain base for it: same `a`, same `h`
(`M₀ = b₀ + h`), same class mod `a` and `b₀ ≤ b` (`(b − b₀) % a = 0` with
`b₀ ≤ b`). Window arithmetic: every table row has `b₀ ≤ 31`, and the window
`[43, 53]` spans a full residue system mod `a` for every `a ≤ 11`, so for
`b ≥ 54` the guard descends along `b ↦ b − a` (`rowFor`); the λ-lift
(the lambda-lift lemma, `FrameCert.lift_iter`) then transports the base certificate to
the target (`sharpTriple_of_base`). Kernel `decide` only.
-/
import Erdos1112Proof.Sharp.TablesData

namespace Erdos1112
namespace Proof

/-- The `(a, h, b)`-conditions satisfied by every Case-B target with
`h := M − b` (Boolean form, for the decided sweep): hard-core shape
(`3 ≤ a`, `1 ≤ h ≤ a−2`, `a < b`, `gcd(a,b) = 1`), the branch conditions
`a ∤ M = b + h` and `a ∤ b + M = 2b + h`, `e = b − a ≠ h`, and
`μ = b − a + h ≥ 12`, together with the Case-B size bound `a ≤ 11`. -/
def caseBGuard (a h b : ℕ) : Bool :=
  decide (3 ≤ a) && decide (a ≤ 11) && decide (1 ≤ h) && decide (h + 2 ≤ a) &&
  decide (a < b) && decide (Nat.gcd a b = 1) &&
  decide ((b + h) % a ≠ 0) && decide ((2 * b + h) % a ≠ 0) &&
  decide (b - a ≠ h) && decide (12 ≤ b - a + h)

/-- Row `(a₀, b₀, M₀, x, Y, Z)` is a usable λ-chain base for the target
data `(a, h, b)`: `a₀ = a`, `b₀ ≤ b`, `b ≡ b₀ (mod a)`, `M₀ = b₀ + h`. -/
def caseBRowMatch (a h b : ℕ) (row : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  decide (row.1 = a) && decide (row.2.1 ≤ b) &&
  decide ((b - row.2.1) % a = 0) && decide (row.2.2.1 = row.2.1 + h)

/-- The bounded completeness sweep: every guard-passing `(a, h, b)` with
`a ≤ 11`, `h ≤ 9`, `b ≤ 53` has a base row in `certTableB`. -/
def caseBComplete : Bool :=
  (List.range 12).all fun a =>
    (List.range 10).all fun h =>
      (List.range 54).all fun b =>
        !(caseBGuard a h b) || certTableB.any (caseBRowMatch a h b)

set_option maxRecDepth 1000000 in
theorem caseBComplete_true : caseBComplete = true := by decide

theorem caseBGuard_eq_true_iff {a h b : ℕ} :
    caseBGuard a h b = true ↔
      3 ≤ a ∧ a ≤ 11 ∧ 1 ≤ h ∧ h + 2 ≤ a ∧ a < b ∧ Nat.gcd a b = 1 ∧
      (b + h) % a ≠ 0 ∧ (2 * b + h) % a ≠ 0 ∧ b - a ≠ h ∧ 12 ≤ b - a + h := by
  simp only [caseBGuard, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem caseBRowMatch_eq_true_iff {a h b : ℕ} {row : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} :
    caseBRowMatch a h b row = true ↔
      row.1 = a ∧ row.2.1 ≤ b ∧ (b - row.2.1) % a = 0 ∧
      row.2.2.1 = row.2.1 + h := by
  simp only [caseBRowMatch, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- Coprimality descends along `b ↦ b − a` (cf. `HardCore.coprime_a_e`). -/
theorem gcd_sub_self_right {a b : ℕ} (hab : a ≤ b) (h : Nat.gcd a b = 1) :
    Nat.gcd a (b - a) = 1 := by
  have h1 : Nat.gcd a (b - a) ∣ a := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd a (b - a) ∣ b - a := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd a (b - a) ∣ b := by
    have h5 : Nat.gcd a (b - a) ∣ b - a + a := Nat.dvd_add h2 h1
    rwa [Nat.sub_add_cancel hab] at h5
  have h4 : Nat.gcd a (b - a) ∣ Nat.gcd a b := Nat.dvd_gcd h1 h3
  rw [h] at h4
  exact Nat.dvd_one.mp h4

/-- Sweep soundness inside the decided window. -/
theorem rowFor_small {a h b : ℕ} (hb : b < 54) (hg : caseBGuard a h b = true) :
    ∃ row ∈ certTableB, caseBRowMatch a h b row = true := by
  obtain ⟨-, ha11, -, hh2a, -⟩ := caseBGuard_eq_true_iff.mp hg
  have hall := caseBComplete_true
  simp only [caseBComplete, List.all_eq_true, List.mem_range] at hall
  have hpt := hall a (by omega) h (by omega) b hb
  rw [hg] at hpt
  simp only [Bool.not_true, Bool.false_or] at hpt
  exact List.any_eq_true.mp hpt

/-- **Completeness for all `b`**: every guard-passing target datum has a
base row in `certTableB`, by descent `b ↦ b − a` into the decided window
(the window `[43, 53]` is a full residue system mod `a`, and all guard
conditions are mod-`a`-stable or slack for `b ≥ 54`). -/
theorem rowFor {a h : ℕ} :
    ∀ b, caseBGuard a h b = true →
      ∃ row ∈ certTableB, caseBRowMatch a h b row = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hg
    by_cases hb : b < 54
    · exact rowFor_small hb hg
    · obtain ⟨h3a, ha11, h1h, hh2a, hab, hgcd, hmod1, hmod2, -, -⟩ :=
        caseBGuard_eq_true_iff.mp hg
      have hab' : a ≤ b := Nat.le_of_lt hab
      -- the guard holds at `b - a`
      have hg' : caseBGuard a h (b - a) = true := by
        rw [caseBGuard_eq_true_iff]
        refine ⟨h3a, ha11, h1h, hh2a, by omega, gcd_sub_self_right hab' hgcd,
          ?_, ?_, by omega, by omega⟩
        · intro hcon
          apply hmod1
          have e1 : b + h = b - a + h + a := by omega
          rw [e1, Nat.add_mod_right]
          exact hcon
        · intro hcon
          apply hmod2
          have e2 : 2 * b + h = 2 * (b - a) + h + a + a := by omega
          rw [e2, Nat.add_mod_right, Nat.add_mod_right]
          exact hcon
      obtain ⟨row, hrow, hmatch⟩ := ih (b - a) (by omega) hg'
      obtain ⟨hra, hrb, hrm, hrM⟩ := caseBRowMatch_eq_true_iff.mp hmatch
      refine ⟨row, hrow, caseBRowMatch_eq_true_iff.mpr ⟨hra, by omega, ?_, hrM⟩⟩
      have hstep : b - row.2.1 = b - a - row.2.1 + a := by omega
      rw [hstep, Nat.add_mod_right]
      exact hrm

/-- A matching base row certifies the target triple: the λ-lift
(`FrameCert.lift_iter` at `lam` with `lam * a = b − b₀`) transports the
row's frame certificate to `(a, b, M)`, which then yields (SHARP). -/
theorem sharpTriple_of_base {a b M : ℕ} {row : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ}
    (hrow : row ∈ certTableB) (hra : row.1 = a) (hrb : row.2.1 ≤ b)
    (hrm : (b - row.2.1) % a = 0) (hrM : row.2.2.1 = row.2.1 + (M - b))
    (hbM : b ≤ M) : SharpTriple a b M := by
  have hframe := certTableB_frame row hrow
  rw [hra] at hframe
  obtain ⟨lam, hlam⟩ := Nat.dvd_of_mod_eq_zero hrm
  have hcomm : lam * a = a * lam := Nat.mul_comm lam a
  have hb' : row.2.1 + lam * a = b := by omega
  have hM' : row.2.2.1 + lam * a = M := by omega
  have hlift := hframe.lift_iter lam
  rw [hb', hM'] at hlift
  exact hlift.sharpTriple

end Proof
end Erdos1112
