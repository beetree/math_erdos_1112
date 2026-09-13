# Lean formalization of Erdős Problem #1112

The [short paper](../paper/erdos1112.pdf) gives the dichotomy with existence ratio
$d_2+2$. This branch is migrating the full formal proof to that argument.

## Statements

The definitions live in [Erdos1112.lean](Erdos1112.lean), and the canonical theorems in
[Erdos1112Proof/Final.lean](Erdos1112Proof/Final.lean):

- `erdos_1112`: `Question k d₁ d₂ ↔ k + 1 ≤ d₂`.
- `erdos_1112_existence_bound`: `RatioWorks k d₁ d₂ (d₂ + 2)` above the threshold.
- `erdos_1112_strong_nonexistence`: below the threshold, every prescribed ratio sequence
  admits one sequence meeting the sumset of every admissible walk.
- `erdos_1112_int`: the dichotomy in the literal integer-ratio formulation.

The hypotheses are `3 ≤ k`, `1 ≤ d₁`, and `d₁ < d₂`. Arbitrary functions `Fin k → ℕ`
index the summands, so repetitions are allowed. Additive gap inequalities avoid
truncated subtraction. `question_iff_questionInt` proves the ratio-formulation bridge.

## Migration status

| New paper argument | Checked implementation |
|---|---|
| Reciprocal interpolation and existence | [Existence/Reciprocal.lean](Erdos1112Proof/Existence/Reciprocal.lean) |
| Coprime rectangle, interlacing, centered frame, two-generator targets | [Short/Intervals.lean](Erdos1112Proof/Short/Intervals.lean) |
| Slots and gcd normalization | [Short/Slots.lean](Erdos1112Proof/Short/Slots.lean), [Short/Normalization.lean](Erdos1112Proof/Short/Normalization.lean) |
| Complete binary growth/covering alternative | [Short/BinaryGrowth.lean](Erdos1112Proof/Short/BinaryGrowth.lean), [Short/Binary.lean](Erdos1112Proof/Short/Binary.lean) |
| SHARP induction reduction and paired movers | [Short/Funnel.lean](Erdos1112Proof/Short/Funnel.lean), [Short/Movers.lean](Erdos1112Proof/Short/Movers.lean) |
| Odd-spacing exceptions | [Short/OddSpacing.lean](Erdos1112Proof/Short/OddSpacing.lean) |
| Finite Kneser theorem | [Short/KneserFinite/](Erdos1112Proof/Short/KneserFinite/) |
| Complete even SHARP residue argument | [Short/EtaEven.lean](Erdos1112Proof/Short/EtaEven.lean) |
| Growth-to-density and iteration, with Kneser explicitly pending | [Short/DensityIteration.lean](Erdos1112Proof/Short/DensityIteration.lean) |
| E-transform density invariance | [Short/KneserDensity/ETransform.lean](Erdos1112Proof/Short/KneserDensity/ETransform.lean) |
| Weak pairwise Kneser law and odd SHARP residue assembly | In progress |

The final non-existence theorem currently retains the earlier implementation. The
new proof must be completed before retiring the old `Sharp/` and `NonEx/` internals.
A successful audit of that theorem certifies the current implementation, not full
correspondence with the new paper.

## Build and audit

With `elan` installed:

```bash
cd lean
lake exe cache get
lake build
lake env lean Erdos1112Proof/AxiomsCheck.lean
```

Keep the dependency pins in `lake-manifest.json` and `lean-toolchain`; do not run
`lake update`. The compiler is Lean 4.27.0. New proof modules can be checked separately:

```bash
lake build Erdos1112Proof.Existence.Reciprocal Erdos1112Proof.Short.Intervals
```

The completed theorem audit must contain only `propext`, `Classical.choice`, and
`Quot.sound`. No unproved assumptions or computational trust axioms may be introduced
for the missing density or finite interval arguments.
