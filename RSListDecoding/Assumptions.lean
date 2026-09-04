import RSListDecoding.Defs.RootAlgorithm

/-!
# External assumptions

This is the sole permitted location for declarations imported from the
literature or justified by an external computation.  The combinatorial
formalization uses the cardinality clause of one published theorem.  The
algorithmic extension additionally uses the algorithmic clause of that same
theorem as its sole external algorithmic input.
-/

namespace RSListDecoding

/-- **External input: Kopparty, Theorem 4.3 (cardinality clause).**

Source: Swastik Kopparty, *List-Decoding Multiplicity Codes*, Theory of
Computing 11(5), 2015, Theorem 4.3, pp. 159--160 and proof pp. 165--167,
<https://theoryofcomputing.org/articles/v011a005/v011a005.pdf>.

For a nonzero `Q(X,Y₀,...,Yᵣ)` over the field of `q` elements, the theorem
bounds its degree-at-most-`D` polynomial solutions after substituting Hasse
derivatives for the jet variables.  Its hypotheses are the individual bounds
`deg_{Y_j} Q ≤ t < q` and weighted degree
`deg_(1,D,D-1,...,D-r) Q < q²`; the conclusion is
`t(r+1)q^(2r⌊D/q⌋+4r+4)`.

The source writes its theorem over `F_q`; the surrounding univariate result
and the displayed `floor (D / q)` estimate are in its prime-order regime.
This declaration therefore uses only `ZMod q` for prime `q`.  We make
`r ≤ D` explicit so every displayed weight has its intended nonnegative
value.  We also make `Q ≠ 0`
explicit: it is assumed at the start of the source proof and is necessary for
the cardinality statement, although it is missing from the displayed theorem
statement.

Consumers should normally use the checked specializations in
`Lemmas/RootCount.lean`, rather than invoking this declaration directly. -/
axiom kopparty_theorem_4_3_cardinality {q r D t : ℕ}
    (hq : Nat.Prime q) (hrD : r ≤ D) (ht : 0 < t)
    (Q : DifferentialPolynomial q r) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (r + 1), Q.degreeOf (some j) ≤ t)
    (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < q ^ 2) :
    (differentialSolutions hq.ne_zero D Q).card ≤
      t * (r + 1) * q ^ (2 * r * (D / q) + 4 * r + 4)

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
