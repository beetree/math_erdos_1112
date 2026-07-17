/-
the subset-sum development certificate layer: the kernel-decidable frame-certificate checker
and its soundness theorem. Certificate DATA lives in `Sharp/TablesData.lean`
(6-tuples `(a, b, M, x, Y, Z)`, split into Table A and Table B).

All 360 table rows satisfy the per-residue frame condition
(`FrameCert`/`frameCertOK`), which is what the λ-lift transports, so one
certificate notion serves validity, lift-stability, and (SHARP)-witnessing
at once. Kernel `decide` only.
-/
import Erdos1112Proof.Sharp.Lift

namespace Erdos1112
namespace Proof

/-- Boolean checker for `FrameCert`, kernel-`decide`-friendly. -/
def frameCertOK : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → Bool
  | (a, b, M, x, Y, Z) =>
    decide (0 < M) && decide (x + Y + Z ≤ M - 1) && decide (Y + Z + 1 ≤ a) &&
    ((List.range a).all fun ρ =>
      (List.range (Y + 1)).any fun j =>
        (List.range (Z + 1)).any fun k =>
          decide ((j * b + k * M) % a = ρ) &&
          decide (M - 1 + (j * b + k * M) ≤ a * x))

/-- **Checker soundness**: a passing row is a genuine frame certificate. -/
theorem frameCertOK_sound {a b M x Y Z : ℕ}
    (h : frameCertOK (a, b, M, x, Y, Z) = true) : FrameCert a b M x Y Z := by
  rw [frameCertOK] at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  refine ⟨h0, h1, h2, ?_⟩
  intro ρ hρ
  obtain ⟨j, hj, k, hk, hres, hht⟩ := h3 ρ hρ
  exact ⟨j, k, by omega, by omega, hres, hht⟩

/-- Convenience: a passing row yields its (SHARP) witness. -/
theorem frameCertOK_sharpTriple {a b M x Y Z : ℕ}
    (h : frameCertOK (a, b, M, x, Y, Z) = true) : SharpTriple a b M :=
  (frameCertOK_sound h).sharpTriple

end Proof
end Erdos1112
