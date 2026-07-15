/-
Axiom audit for the three target theorems of Erdős Problem #1112.

`lake build` compiles this file as its last step and prints, for each of the
three theorems, the axioms its proof depends on. The whole development is
`sorry`-free, so only Lean's three standard foundational axioms appear.
-/
import Erdos1112Proof.Final
#print axioms Erdos1112.erdos_1112
#print axioms Erdos1112.erdos_1112_existence_bound
#print axioms Erdos1112.erdos_1112_strong_nonexistence
#print axioms Erdos1112.erdos_1112_int
#print axioms Erdos1112.question_iff_questionInt
