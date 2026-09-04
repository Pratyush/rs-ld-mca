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

/-- **External input: the degree-below-characteristic refinement of
Kopparty, Theorem 4.3 (cardinality clause).**

Source: Swastik Kopparty, *List-Decoding Multiplicity Codes*, Theory of
Computing 11(5), 2015, Theorem 4.3, pp. 159--160 and proof pp. 165--167,
<https://theoryofcomputing.org/articles/v011a005/v011a005.pdf>.

For a nonzero `Q(X,Y₀,...,Yᵣ)` over the field of `q` elements, the theorem
bounds its degree-at-most-`D` polynomial solutions after substituting Hasse
derivatives for the jet variables.  We use the following direct refinement
of the proof in the special regime `D < q` needed by this project.  If the
weighted degree is smaller than `q^e`, then the number of solutions is at
most

`t * sum_{j=0}^r q^(e(j+1))`.

Here is the refinement of the count on pp. 165--167.  Run `SOLVE` over the
degree-`e` extension.  Since `D < q`, every binomial coefficient used in the
Hensel lift is nonzero modulo the characteristic, so a nonsingular initial
jet has at most one lift: the generic `q^(2r floor(D/q)+2r)` branching factor
is exactly one.  Stratify the recursion by the first nonvanishing partial
derivative in its current highest jet variable.  For fixed values of the
base point and all lower jets, these strata are disjoint roots of one
univariate polynomial and have total cardinality at most `t`.  There are
`q^(e(j+1))` choices at order `j`.  Summing over the possible highest jet
variables gives the displayed geometric sum.  It is strictly smaller than
the coarser `t(r+1)q^(e(r+1))` bound.

Taking `e=2` improves the literal bound obtained by substituting `D<q` into
the displayed statement of Theorem 4.3 from `t(r+1)q^(4r+4)` to a value below
`2tq^(2r+2)`.  If the weighted degree is already below `q`, taking `e=1`
gives a value below `2tq^(r+1)` and avoids the quadratic extension.

The source writes its theorem over `F_q`; the surrounding univariate result
and the displayed `floor (D / q)` estimate are in its prime-order regime.
This declaration therefore uses only `ZMod q` for prime `q`.  We make
`r ≤ D` explicit so every displayed weight has its intended nonnegative
value.  We also make `Q ≠ 0`
explicit: it is assumed at the start of the source proof and is necessary for
the cardinality statement, although it is missing from the displayed theorem
statement.

Downstream consumers should normally use the checked specializations in
`Lemmas/RootCount.lean`, rather than invoking this declaration directly. -/
axiom kopparty_degree_lt_characteristic_cardinality {q r D t e : ℕ}
    (hq : Nat.Prime q) (hrD : r ≤ D) (hDq : D < q)
    (ht : 0 < t) (he : 0 < e)
    (Q : DifferentialPolynomial q r) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (r + 1), Q.degreeOf (some j) ≤ t)
    (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < q ^ e) :
    (differentialSolutions hq.ne_zero D Q).card ≤
      t * rootCountGeometricFactor q e r

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
