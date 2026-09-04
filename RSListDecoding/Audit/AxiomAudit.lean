import RSListDecoding.Main
import RSListDecoding.Lemmas.RootCount
import RSListDecoding.Lemmas.QuadraticMultiplicity

/-!
# Kernel trust audit

This module is imported by the library root, so its checks run in every full
build.  The proposition definitions and the paper-owned interpolation solver
have no project-specific assumptions.  The combinatorial capstone uses only
Kopparty's cardinality clause.  Decoder correctness uses only Kopparty's
algorithmic clause, while the final algorithmic capstone uses both clauses.
-/

/--
info: 'RSListDecoding.CombinatorialMainStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.CombinatorialMainStatement

/--
info: 'RSListDecoding.combinatorial_main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RSListDecoding.kopparty_theorem_4_3_cardinality]
-/
#guard_msgs in
#print axioms RSListDecoding.combinatorial_main

/- The interpolation construction is paper-owned and must remain independent
of the external root-counting input. -/
/--
info: 'RSListDecoding.exists_scoped_ambient_explainer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.exists_scoped_ambient_explainer

/--
info: 'RSListDecoding.differentialSolutions_card_le_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RSListDecoding.kopparty_theorem_4_3_cardinality]
-/
#guard_msgs in
#print axioms RSListDecoding.differentialSolutions_card_le_public

/--
info: 'RSListDecoding.AlgorithmicMainStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.AlgorithmicMainStatement

/- The checked Gaussian solver and interpolation phase must not acquire an
external algorithmic assumption. -/
/--
info: 'RSListDecoding.GaussianKernel.solve_result_mem_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.GaussianKernel.solve_result_mem_kernel

/--
info: 'RSListDecoding.solveInterpolationConstraints_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.solveInterpolationConstraints_satisfies

/--
info: 'RSListDecoding.decoderProgram_result_eq_decodingList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RSListDecoding.kopparty_theorem_4_3_algorithm]
-/
#guard_msgs in
#print axioms RSListDecoding.decoderProgram_result_eq_decodingList

/--
info: 'RSListDecoding.algorithmic_main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RSListDecoding.kopparty_theorem_4_3_algorithm,
 RSListDecoding.kopparty_theorem_4_3_cardinality]
-/
#guard_msgs in
#print axioms RSListDecoding.algorithmic_main

/-! ## Free-derivative-order strengthening -/

/- The new analytic threshold and interpolation construction introduce no
additional project-specific assumptions. -/
/--
info: 'RSListDecoding.exists_freeOrderThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.exists_freeOrderThreshold

/--
info: 'RSListDecoding.exists_freeOrder_ambient_explainer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.exists_freeOrder_ambient_explainer

/--
info: 'RSListDecoding.AllRateCombinatorialMainStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.AllRateCombinatorialMainStatement

/--
info: 'RSListDecoding.all_rate_combinatorial_main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RSListDecoding.kopparty_theorem_4_3_cardinality]
-/
#guard_msgs in
#print axioms RSListDecoding.all_rate_combinatorial_main

/--
info: 'RSListDecoding.AllRateAlgorithmicMainStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.AllRateAlgorithmicMainStatement

/--
info: 'RSListDecoding.all_rate_algorithmic_main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RSListDecoding.kopparty_theorem_4_3_algorithm,
 RSListDecoding.kopparty_theorem_4_3_cardinality]
-/
#guard_msgs in
#print axioms RSListDecoding.all_rate_algorithmic_main

/-! ## Quadratic-multiplicity optimization -/

/- The multiplicity-generic finite capstone, exact shell specialization, and
continuous feasibility calculation use no additional project assumptions. -/
/--
info: 'RSListDecoding.exists_quadratic_weight_and_simplex_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.exists_quadratic_weight_and_simplex_coefficients

/--
info: 'RSListDecoding.exactQuadraticShellFactor_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.exactQuadraticShellFactor_spec

/--
info: 'RSListDecoding.total_contactEnvelope_finrank_lt_interpolationSpace_of_generalScalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.total_contactEnvelope_finrank_lt_interpolationSpace_of_generalScalar

/--
info: 'RSListDecoding.exists_quadratic_weight_coefficient_near_optimal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.exists_quadratic_weight_coefficient_near_optimal

/--
info: 'RSListDecoding.finrank_contactEnvelopeSpace_le_divisible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.finrank_contactEnvelopeSpace_le_divisible

/--
info: 'RSListDecoding.total_contactEnvelope_finrank_lt_interpolationSpace_quadraticScalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.total_contactEnvelope_finrank_lt_interpolationSpace_quadraticScalar

/- The adaptive count and interpolation layers are assumption-free; the
public list-size conclusion uses only Kopparty's cardinality clause. -/
/--
info: 'RSListDecoding.total_coupledContactEnvelope_finrank_lt_interpolationSpace_adaptive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms RSListDecoding.total_coupledContactEnvelope_finrank_lt_interpolationSpace_adaptive

/--
info: 'RSListDecoding.quadratic_adaptive_combinatorial_main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 RSListDecoding.kopparty_theorem_4_3_cardinality]
-/
#guard_msgs in
#print axioms RSListDecoding.quadratic_adaptive_combinatorial_main
