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

For every fixed `0 < ε < 1` and `0 < θ < 1`, the strengthened statements
provide a threshold `d₀(ε, θ)` such that every `d ≥ d₀` works for all
dimensions `k ≤ floor ((1-θ) ε n)`, subject to the same explicit root-finding
field conditions.  Thus every fixed rate strictly below agreement is covered;
the resulting threshold is not claimed to be practical.  The strengthened
capstones retain the exact list bound
`B * (d + 1) * q^(4*d+4)` and the decoder bound `q^(C*(d+1))`, rather than
absorbing these into the manuscript's coarser public exponents.

The free-order assembly now keeps the floor and shell-ceiling ratios exact,
counts the local contact region as a triangle, and counts the three global
slack variables by their shared simplex of total width
`floor(θ*d^3/4)`.  The resulting asymptotic rank
coefficient is `θ^3/384`, versus `θ^3/110592` in the previous rectangular
assembly—a factor `288` improvement.  This materially reduces the formal
large-order threshold, although it does not by itself make that threshold
practical at cryptographic block lengths.

The shell-ratio estimate is also sharpened from the slack power
`d^((5-θ)/(5+θ))` to the explicit bound
`(2*exp(3))*d^(2/(2+θ))`.  Consequently the rank-saving exponent improves
from `2θ/(5+θ)` to `θ/(2+θ)`.  This is the limiting exponent of the present
shell argument; the main all-rate theorem uses the new rounded factor
directly, including its exact finite-order ceiling.

The only project-specific assumptions are the cardinality and algorithmic
clauses of Kopparty's Theorem 4.3, both declared and documented in
`RSListDecoding/Assumptions.lean`. The kernel dependency checks are in
`RSListDecoding/Audit/AxiomAudit.lean`.

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
