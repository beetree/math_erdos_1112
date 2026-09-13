/-
Axiom audit for the ported finite Kneser theorem (`Finset.mul_kneser` /
`Finset.add_kneser`, and their strict counterparts). `lake build` compiles this
file as the last step of the `KneserFinite` port and prints the axioms each
theorem's proof depends on: it should be only Lean's three standard
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), with no
`sorryAx` and no `native_decide` witnesses.
-/
import Erdos1112Proof.Short.KneserFinite.FinsetKneserTheorem

#print axioms Finset.mul_kneser
#print axioms Finset.add_kneser
#print axioms Finset.mul_strict_kneser
#print axioms Finset.add_strict_kneser
