import Erdos1112Proof.Short.KneserMinima
import Erdos1112Proof.Short.KneserGridAssembly
import Erdos1112Proof.Short.KneserFiniteRight
import Erdos1112Proof.Short.KneserSpacing
import Erdos1112Proof.Short.Sharp
import Erdos1112Proof.Short.KneserConcrete
import Erdos1112Proof.Short.KneserBlocks
import Erdos1112Proof.Short.KneserStabilization
import Erdos1112Proof.Short.KneserCompressionSequence
import Erdos1112Proof.Short.KneserMann
import Erdos1112Proof.Short.KneserGrid
import Erdos1112Proof.Short.KneserResidues
import Erdos1112Proof.Short.KneserCompression
import Erdos1112Proof.Short.KneserShift
import Erdos1112Proof.Short.SharpAssembly
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
import Erdos1112Proof.Short.ResidueFrame
import Erdos1112Proof.Short.EvenBudget
import Erdos1112Proof.Short.OddBudget
import Erdos1112Proof.Short.DensityLimit
import Erdos1112Proof.Short.KneserSequence
import Erdos1112Proof.Short.DensityIteration
import Erdos1112Proof.Short.KneserDensity.ETransform
import Erdos1112Proof.Short.EtaEven
import Erdos1112Proof.Short.Funnel
import Erdos1112Proof.Short.OddSpacing
import Erdos1112Proof.Short.Movers
import Erdos1112Proof.Short.BinaryGrowth
import Erdos1112Proof.Short.KneserFinite.FinsetKneserTheorem
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
#print axioms Erdos1112.Proof.Short.spacing_one
#print axioms Erdos1112.Proof.Short.spacing_two
#print axioms Finset.add_kneser
#print axioms Finset.add_strict_kneser

#print axioms Erdos1112.Proof.Short.paired_movers
#print axioms Erdos1112.Proof.Short.binary_dichotomy

#print axioms Erdos1112.Proof.Short.residue_frame_pos_run
#print axioms Erdos1112.Proof.Short.residue_frame_neg_run
#print axioms Erdos1112.Proof.Short.path_K_le
#print axioms Erdos1112.Proof.Short.even_budget_eta_minus
#print axioms Erdos1112.Proof.Short.even_budget_eta_plus
#print axioms Erdos1112.Proof.Short.count_bound_of_growth

#print axioms Erdos1112.Proof.Short.odd_budget_eta_two
#print axioms Erdos1112.Proof.Short.odd_budget_eta_neg2_ge3
#print axioms Erdos1112.Proof.Short.odd_budget_eta_n
#print axioms Erdos1112.Proof.Short.KneserDensity.fair_of_least_choices
#print axioms Erdos1112.Proof.Short.KneserDensity.finite_absorption
#print axioms Erdos1112.Proof.Short.KneserDensity.progression_of_limit
#print axioms Erdos1112.Proof.Short.KneserDensity.finite_prefix_eventually_deleted

#print axioms Erdos1112.Proof.Short.KneserDensity.arbitrary_progressions_of_pairs

#print axioms Erdos1112.Proof.Short.KneserDensity.transformSequence_fair
#print axioms Erdos1112.Proof.Short.KneserDensity.transformSequence_score
#print axioms Erdos1112.Proof.Short.KneserDensity.transformSequence_sum_subset

#print axioms Erdos1112.Proof.Short.eta_even
#print axioms Erdos1112.Proof.Short.lowerDensity_range_ge_inv_of_growth
#print axioms Erdos1112.Proof.Short.add_lowerDensity_le_twoFoldLowerDensity
#print axioms Erdos1112.Proof.Short.density_iterate
#print axioms Erdos1112.Proof.Short.tailCovering_of_growth_lt
#print axioms Erdos1112.Proof.Short.KneserDensity.twoFoldLowerDensity_eTransform_eq

#print axioms Erdos1112.Proof.Short.KneserMann.mann_count
#print axioms Erdos1112.Proof.Short.KneserDensity.finite_grid_of_pairs
#print axioms Erdos1112.Proof.Short.KneserDensity.bounded_residue_frame
#print axioms Erdos1112.Proof.Short.KneserDensity.realization_of_modular_subset_sums
#print axioms Erdos1112.Proof.Short.exists_modular_cover
#print axioms Erdos1112.Proof.Short.exists_stable_residues
#print axioms Erdos1112.Proof.Short.KneserCompression.compressedSet_add
#print axioms Erdos1112.Proof.Short.KneserCompression.posCount_compressedSet_eq_add_O1
#print axioms Erdos1112.Proof.Short.lowerDensity_shiftedDown
#print axioms Erdos1112.Proof.Short.twoFoldLowerDensity_shiftedDown_both
#print axioms Erdos1112.Proof.Short.HasAPTail.of_shiftedDown_add
#print axioms Erdos1112.Proof.Short.sharpTriple_of_paired_movers
#print axioms Erdos1112.Proof.Short.sharp_all_of_odd

#print axioms Erdos1112.Proof.Short.eta_odd
#print axioms Erdos1112.Proof.Short.sharp_all
#print axioms Erdos1112.Proof.Short.KneserDensity.fair_Aseq_Bseq
#print axioms Erdos1112.Proof.Short.KneserDensity.twoFoldLowerDensity_Aseq_Bseq
#print axioms Erdos1112.Proof.Short.KneserDensity.lane_theorem13_absorbed
#print axioms Erdos1112.Proof.Short.stabilization_bundle
#print axioms Erdos1112.Proof.Short.KneserCompression.compressed_fair
#print axioms Erdos1112.Proof.Short.KneserCompression.hasAPTail_of_compressed_cofinite

#print axioms Erdos1112.Proof.Short.KneserDensity.classMin_Aseq_eq_of_multiples
#print axioms Erdos1112.Proof.Short.KneserDensity.interval_of_scaled_cover
#print axioms Erdos1112.Proof.Short.KneserFiniteRight.twoFoldLowerDensity_eq_lowerDensity_of_finite_right
#print axioms Erdos1112.Proof.Short.KneserDensity.transformSequence_sum_antitone
