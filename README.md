# Reed--Solomon list-decoding Lean certificate

This is the source-only Lean certificate for the combinatorial and algorithmic
Reed--Solomon list-decoding theorems. It does not contain Mathlib, the local
`.lake` build/cache directory, the LaTeX manuscript, generated PDFs, editor
configuration, or Git history.

The exact propositions are in `RSListDecoding/Statements.lean`. The short
trusted surface is `RSListDecoding/Main.lean`:

- `RSListDecoding.combinatorial_main` proves the list-size theorem.
- `RSListDecoding.algorithmic_main` proves exact decoder correctness and the
  finite-field-operation bound.
- `RSListDecoding.all_rate_combinatorial_main` strengthens the paper's
  low-rate theorem by choosing the Hasse-derivative order independently of
  the agreement parameter.
- `RSListDecoding.all_rate_algorithmic_main` gives the corresponding decoder
  and operation bound.
- `RSListDecoding.quadratic_adaptive_combinatorial_main` gives the exact
  finite quadratic-multiplicity certificate.
- `RSListDecoding.quadratic_adaptive_base_field_combinatorial_main` gives its
  smaller-list specialization when the weighted degree is below `q`.

For every fixed `0 < ε < 1` and `0 < θ < 1`, the strengthened statements
provide a threshold `d₀(ε, θ)` such that every `d ≥ d₀` works for all
dimensions `k ≤ floor ((1-θ) ε n)`, subject to the same explicit root-finding
field conditions.  Thus every fixed rate strictly below agreement is covered;
the resulting threshold is not claimed to be practical.  The strengthened
capstones retain the exact list bound
`B * sum_{j=0}^d q^(2*(j+1))` and the decoder bound `q^(C*(d+1))`, rather than
absorbing these into the manuscript's coarser public exponents.

The free-order assembly keeps all finite ratios exact, counts the local
contact region as a triangle, and counts the three global slack variables by
a shared simplex.  Its width is now
`floor(λ(θ)*d^3)`, where
`λ(θ)=min(1, θ*(1+3θ)/(4*(1-θ)))`, the largest uniform width allowed by the
current higher-jet cutoff.  The limiting simplex-volume coefficient is
`λ(θ)^3/6`, strictly larger than the former `θ^3/384` for every
`0 < θ < 1`.

The capstone uses the exact smallest natural shell factor
`ceilDiv(2*(W+N)^(d-1), W^(d-1))`, where
`N=d^3+d*(d-1)/2`.  Lean proves both its defining inequality and its
minimality.  It is bounded by the analytic factor
`ceil((2*exp(3))*d^(2/(2+θ)))`, so the rank-saving exponent remains the sharp
`θ/(2+θ)` without paying that analytic constant at finite parameters.

For the quadratic schedule `m=c*d^2`, the certificate now also optimizes the
rank coefficient.  At a requested saving exponent `β<θ`, define

~~~text
Λ(θ,β,c) = min(1,
  1/(1-θ) - (1+1/(2c))/(1-β)).
~~~

Every normalized simplex width `λ<Λ(θ,β,c)` is feasible, and every feasible
width is at most `Λ(θ,β,c)`.  Because `d` divides `m`, the exact triangular
contact count removes the generic factor two: the finite rank quotient is
`c*d^2 / ((c*d+1)*R)`, asymptotic to `d/R` rather than `d/(2R)`.  Hence the
supremal limiting rank coefficient is `Λ(θ,β,c)^3/6`.  Choosing width
`(1-δ)Λ` retains exactly the fraction `(1-δ)^3` of this coefficient.

The finite quadratic theorem now avoids both remaining worst-case
replacements.  Its local certificate is the contact-layer sum

~~~text
sum_{t+d*b<m} (m+t+1) * N_d(W+t+d*b),
~~~

and its global certificate is the degree-adaptive sum

~~~text
(K-1) * sum_{e in G} choose(J(e)+2,3),
~~~

where `J(e)` is the exact residual width left by the multiplicity, ordinary
degree, and weighted-degree budgets.  Lean proves that the local constraint
map lands in this coupled envelope, that the adaptive global monomials are
eligible and distinct, and that comparison of these two computable sums
implies the sharp Reed--Solomon list bound.  This is exported as
`quadratic_adaptive_combinatorial_main`.  It is a finite certificate theorem;
an eventual closed-form estimate for the two adaptive sums is intentionally
not asserted here.

The list-size analysis also specializes Kopparty's root recursion to the
degree-below-characteristic regime used here.  There is no characteristic
branching in the Hensel lift, reducing the quadratic-extension bound from
`B*(d+1)*q^(4*d+4)` to `B*sum_{j=0}^d q^(2*(j+1))`.  Under the stronger and often
practical condition `m*A ≤ q`, the recursion runs over the base field and the
bound becomes `B*sum_{j=0}^d q^(j+1)`.  The latter conclusion is exported by
`quadratic_adaptive_base_field_combinatorial_main`.

The refined cardinality analysis is proved internally in
`RSListDecoding/Lemmas/RootRefinement.lean`.  The only remaining
project-specific assumption is the algorithmic clause of Kopparty's
Theorem 4.3, declared in `RSListDecoding/Assumptions.lean`.  The kernel
dependency checks are in `RSListDecoding/Audit/AxiomAudit.lean`.

`ROOT_REFINEMENT.md` gives the mathematical proof mirrored by the Lean
cardinality development.
`scripts/exact_quadratic_evaluator.py` evaluates the finite quadratic
certificate using exact integers; see `scripts/README.md` for the generating
function identity, resource guard, and brute-force cross-checks.

## Verification

Install `elan`, then run:

~~~bash
lake exe cache get
lake build --wfail
lake env lean --trust=0 RSListDecoding/Main.lean -DwarningAsError=true
./scripts/check-trust.sh
~~~

The first command downloads Mathlib's compiled cache outside the certificate
sources. The pinned versions are recorded in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`.

The runtime theorem counts base-field additions, subtractions, negations,
multiplications, inversions, and equality tests. It is not a bit-complexity,
memory-use, or wall-clock-time claim.
