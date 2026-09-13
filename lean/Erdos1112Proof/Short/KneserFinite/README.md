# Finite Kneser dependency

These files prove finite Kneser and its strict refinement. They do not prove
Kneser's asymptotic-density theorem.

The port preserves the Apache 2.0 copyright notices of Mantas Bakšys and Yaël
Dillies. The input snapshot was copied from the local SolveMath corpus files
`SolveMath/Corpus/NumberTheory/FinsetKneserTheorem.lean` and
`SolveMath/Corpus/NumberTheory/FinsetMulStabilizer.lean` in the
`worker-3/campaign/gate-fix` checkout. The source headers identify their Mathlib
lineage; this project does not assert an upstream revision for that snapshot.
The repository root LICENSE contains the Apache 2.0 terms.

Changes adapt module/import syntax and unavailable helper APIs to the pinned
Lean 4.27.0 and Mathlib revision. The mathematical arguments are retained.
`AxiomsCheck.lean` audits both additive and multiplicative versions, including
strict refinements; the root audit also checks the two additive declarations.
