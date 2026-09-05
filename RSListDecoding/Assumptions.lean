import RSListDecoding.Defs.RootAlgorithm

/-!
# External assumptions

This is the sole permitted location for declarations imported from the
literature or justified by an external computation.  The cardinality clause
of Kopparty's root theorem is proved internally in
`Lemmas/RootRefinement.lean`; only its algorithmic clause remains external.
-/

namespace RSListDecoding

/-- **External input: Kopparty, Theorem 4.3 (algorithmic clause).**

The same source states that the complete solution set above can be found in
time `q^{O(r + rD/q + 1)}`.  `KoppartyAlgorithmicTheorem` gives that statement
an exact meaning in this project's finite-field-operation model: one absolute
constant works uniformly for all valid inputs, the returned finite set is
exactly `differentialSolutions`, and its operation count is bounded by the
corresponding power of `q`.

This is the sole external algorithmic input.  In particular, interpolation
matrix construction, Gaussian elimination, and final filtering are not
included in this declaration. -/
axiom kopparty_theorem_4_3_algorithm : KoppartyAlgorithmicTheorem

end RSListDecoding
