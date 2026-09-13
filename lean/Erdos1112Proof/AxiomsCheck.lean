/-
Axiom audit for the three target theorems of Erdős Problem #1112.

`lake build` compiles this file as its last step and prints, for each of the
three theorems, the axioms its proof depends on. The whole development is
`sorry`-free, so only Lean's three standard foundational axioms appear.
-/
import Erdos1112Proof.Final
import Erdos1112Proof.Short.Intervals
import Erdos1112Proof.Short.Slots
import Erdos1112Proof.Short.Normalization
import Erdos1112Proof.Short.Binary
import Erdos1112Proof.Short.Density
import Erdos1112Proof.Short.Funnel
#print axioms Erdos1112.erdos_1112
#print axioms Erdos1112.erdos_1112_existence_bound
#print axioms Erdos1112.erdos_1112_strong_nonexistence
#print axioms Erdos1112.erdos_1112_int
#print axioms Erdos1112.question_iff_questionInt

-- Audit the checked replacements independently of the legacy final theorem.
#print axioms Erdos1112.Proof.reciprocal_interpolation
#print axioms Erdos1112.Proof.Short.coprime_rectangle
#print axioms Erdos1112.Proof.Short.interlacing
#print axioms Erdos1112.Proof.Short.two_generator_target
#print axioms Erdos1112.Proof.Short.centered_frame
#print axioms Erdos1112.Proof.Short.slots_from_run
#print axioms Erdos1112.Proof.Short.normalize_tail
#print axioms Erdos1112.Proof.Short.normalized_walk
#print axioms Erdos1112.Proof.Short.binary_eventual_width
#print axioms Erdos1112.Proof.Short.binary_tail_covering
#print axioms Erdos1112.Proof.Short.exists_index_le_of_growth
#print axioms Erdos1112.Proof.Short.tailCovering_of_eventually_periodic
#print axioms Erdos1112.Proof.Short.sharpAt_of_funnel
