# Concrete-efficiency research directions

This note records what survived exact calculation after the root-count audit
and the finite evaluator implementation.  “Priority” measures expected
impact on the smallest block length or on the remaining formal trust surface,
not elegance.

## Exact baseline

The finite certificate is

```text
n * L(d,m,W) < G(d,m,W,C,A,K,B),

L = sum_{t+d*b<m} (m+t+1) N_d(W+t+d*b),

G = (K-1) sum_h g_{d,W,C}(h)
                  choose(min(m,B-h,floor(m*A/(K-1))-h)+2,3),
```

where `N_d(z)` counts vectors with weighted sum at most `z`, and
`g_{d,W,C}(h)` counts such vectors of ordinary degree exactly `h`.

For constant adaptive slack, the new evaluator uses the exact identity

```text
sum_h g_{d,W,C}(h)
  = sum_{w=0}^W [x^w] [C+d-1 choose d-1]_x.
```

Thus the good shell is a Gaussian-binomial rectangle: partitions with at
most `C` parts, each at most `d-1`.  This reduces that computation to
`O(dW)` exact integer updates.  The local count is also `O(d(W+m))`, after
aggregating contact pairs by `r=t+d*b`.

Representative exact ratios `G/(nL)` for `c=32` are:

| `(R, epsilon)` | `a` | `d=8` | `d=16` | `d=24` | `d=32` |
|---|---:|---:|---:|---:|---:|
| `(.10,.30)` | `2.00` | 0.06170 | 0.08584 | 0.10511 | 0.12184 |
| `(.10,.20)` | `1.00` | 0.02685 | 0.02553 | 0.02488 | 0.02452 |
| `(.05,.10)` | `1.00` | 0.01342 | 0.01277 | 0.01244 | 0.01226 |
| `(.08,.10)` | `0.25` | 0.000517 | 0.000047 | 0.0000096 | 0.0000029 |

The first row improves with `d` but remains far below one.  The other rows
sit on the largest constant-slack value of `a`; finite `c` makes the shell
exponent slightly unfavorable there.  The genuinely adaptive calculation
does better at small order—for `(.10,.20)`, `d=6`, the best tested `a=1.3`
raises the ratio to `0.03279`—but requires a bivariate big-integer table.
Increasing `c` has almost saturated by `c=32`: at `(.10,.30),d=20,a=2`,
the ratios for `c=2,4,8,16,32,64,128` are respectively
`0.09483, 0.09539, 0.09567, 0.09581, 0.09588, 0.09592, 0.09594`.

## P0.1: root refinement -- proved

`RootRefinement.lean` now proves the extension-field coverage lemma, regular
Hensel-lift uniqueness for `D<q`, multiplicity strata in the current highest
jet, the exact fibre bound, and descent to base-field coefficient vectors.
Mathlib's `GaloisField q e` supplies the extension and cardinality facts.  The
old refined-cardinality and extension-cardinality assumptions have both been
removed, and the kernel audit admits only Mathlib's standard logical axioms.

### Expansion-point amortization

The proof also gives the following stronger statement.  If the interpolation
weighted degree is at most `Delta<q^e`, double-counting regular pairs gives

```text
(q^e-Delta) * #solutions
  <= t * sum_{j=0}^r q^(e*(j+1)).
```

When the field has a fixed margin, say `Delta <= (1-rho)q^e`, this removes a
full `q^e` factor up to `1/rho`: the quadratic-extension exponent drops from
the scale `q^(2r+2)` to `q^(2r)`, and the base-field exponent from `q^(r+1)`
to `q^r`.  It improves list size, not the interpolation rank inequality.  It
is now proved in Lean and propagated through the differential-solution,
decoding-list, explainer, and explicit quadratic-certificate layers.

## P0.2: one-variable adaptive evaluator -- implemented

The general global sum is the main computational target.  Writing `h` for
higher-jet degree and `s` for the three-dimensional simplex slack,
`choose(J(h)+2,3)` counts triples of total degree `<J(h)`.  Consequently the
whole adaptive sum is a coefficient sum of

```text
product_{i=1}^{d-1} 1/(1-y*x^i) * 1/(1-y)^3
```

under one `x` cutoff and several `y` cutoffs, including the separate `s<m`
condition.  `scripts/exact_quadratic_evaluator.py` evaluates the exact sum by
a rolling one-variable Gaussian-binomial recurrence.  It stores `O(W)`
coefficients and performs `O(W*min(C,cap,W))` exact coefficient updates.
Exhaustive small-instance tests compare it against the independent bivariate
dynamic program.  A quasi-linear truncated-product implementation remains a
performance direction, not a correctness obligation for this evaluator.

## P0.3: certified finite threshold search -- sharpened witness found

`scripts/scan_quadratic_parameters.py` emits complete explicit-integer tuples
for the Lean theorem, exact local and global sums, every side-condition, and
the strict certificate comparison.  Decimal logarithms only propose an
integer `W`, with a higher-precision stability check; the theorem input is the
reported integer and contains no logarithm.

The stronger signed-invariant support envelope now gives a passing tuple at
`(R,epsilon,c,a,d)=(.33,.999,32,2,49)`, with `n=100000`, `q=232607`, and
exact ratio `G/(nL)=1.0112755`.  The paper's kernel-subtracted expression
passes already at `d=48`, with ratio `1.0044872`, but its `K_r` direct-sum
rank proof has not yet been ported to Lean.  See
`OPTIMIZATION_AUDIT_2026-09-05.md` for the full integers and reproduction
commands.

## P0.4: unconditional quadratic family -- finite witness, uniform gap remains

Lean now exports `explicit_adaptive_listDecodable_of_exact_sum`, its
base-field variant, and an expansion-point-amortized variant.  Their inputs
are explicit natural numbers, exact finite sums, and decidable arithmetic
hypotheses.  This closes the theorem-interface work but remains conditional
on the strict exact-sum comparison.

A finite tuple now passes the sharpened Lean theorem's arithmetic hypothesis.
Turning the external big-integer calculation into a closed Lean theorem still
requires checking that one displayed inequality inside the kernel, for
example by a verified evaluator or a generated proof certificate.  A uniform
family theorem still needs a lower bound for the Gaussian rectangle shell
strong enough to prove the comparison for all large `d`.

## P0.5: algorithmic theorem -- axiom-free interface, extraction open

The project-specific algorithmic axiom has been removed.  The current
`FieldCost` type, however, is an extensional pair of a mathematical result and
an operation allowance.  It can certify the exact solution set and charge
Kopparty's stated bound without representing an executable recursion.  The
kernel audit therefore proves absence of project axioms, not extraction of
`SOLVE`.

The high-priority remaining work is to strengthen `FieldCost` to an execution
trace or circuit semantics and implement Kopparty's recursion there: enumerate
initial jets, select the highest active ordinary derivative, perform the
regular Hensel lift, recurse on the characteristic branch, and prove coverage,
termination, and the recurrence for charged operations.  Until that is done,
the algorithmic capstone is mathematically extensional rather than an
executable decoder.

## P1: direct restricted-partition asymptotics

The old shell comparison pays the coordinate-rounding slack
`d(d-1)/2`.  Under `m=c*d^2` this becomes the extra exponent `1/(2c)` and is
exactly why the constant-slack boundary fails for `epsilon/R=2` at finite
`c`.  The Gaussian-binomial identity shows the right analytic object is a
partition in a `C` by `d-1` rectangle, not an ordinary simplex plus a worst
case residue box.

The desired theorem is a uniform saddle-point bound for

```text
N_d(W+m) /
  sum_{w<=W} [x^w] [C+d-1 choose d-1]_x.
```

Removing the artificial `d^2/2` shift would both improve the finite constant
and reopen `m=o(d^2)`.  Under the current residue argument, taking
`m=d^(2-gamma)` makes `d^2/m=d^gamma`, producing a superpolynomial shell
penalty; no optimization of `c` repairs that.  This is the only identified
route that plausibly changes the quadratic multiplicity exponent itself.

## P1: stronger local rank via cross-layer syzygies

The exact contact count has leading coefficient

```text
integral_{x+y<1} (1+x) dx dy = 2/3,
```

so its unweighted scale is `(2/3)m^3/d`.  This is the same leading constant
as the kernel calculation in the source paper; the branch has already
captured the obvious triangular saving.  Another constant-factor cleanup is
not enough for the tight regimes.

A useful result must find dependencies between different contact orders,
not merely within a fixed `T` layer.  Algebraically, compute the Hilbert
series of the image of the substitution map, or a Gröbner basis for its
initial module, instead of bounding it by the support envelope.  The target
should be stated before doing the algebra: an additional factor `d^eta` in
local rank changes the threshold exponent; a fixed factor does not.

## P2: several interpolation equations -- negative finite evidence

The interpolation kernel generally contains many independent polynomials,
so producing `Q_1,...,Q_s` is cheap.  It does not follow that their common
differential solution set is smaller.  For example, the independent
polynomials

```text
Q_i(X,Y_0,...,Y_r) = X^i Y_r
```

all have the same `q^r` degree-`<q` solutions `P` with `P^(r)=0`.  More
generally, a large interpolation kernel can lie inside a principal ideal.
Thus “use more equations” has no worst-case gain without a transversality or
gcd statement.

The new exact small-field harness exhaustively checked 1,250 received words
across two `q=5,n=4` configurations.  In every nonempty-kernel case, some
basis interpolant already had exactly the common zero set; multiple equations
never improved on that best basis element.  Some worse basis elements did
have extra roots.  This is evidence, not a theorem, but it reinforces the
principal-ideal obstruction.

The viable version is quotient-rank: prove that the interpolation kernel has
large image modulo every low-weight principal differential ideal.  If that
holds, choose successive `Q_i` outside the differential radical of the
previous equations and seek a dimension drop in initial-jet space.  Until
such a lemma exists, multiple interpolation should not displace the two P1
directions.

## P2: extract a linear differential equation

Fast differential-equation solvers apply to equations

```text
Q_tilde(X) + sum_i Q_i(X)Y_i = 0.
```

They return an affine solution space of dimension at most the differential
order and run in near-linear polynomial arithmetic time.  This is explicit
in Goyal--Harsha--Kumar--Shankar and in the 2025 list-recovery follow-up.
The current hidden-derivative interpolation obtains its dimension advantage
from nonlinear higher-jet monomials, so simply imposing jet-linearity throws
away the partition factor that makes the rank comparison work.

The plausible hybrid is to construct nonlinear `Q`, then prove that every
large solution component forces a low-weight linear differential factor or
a linear equation in the differential ideal generated by several
interpolants.  That would replace Kopparty enumeration by a fast affine-space
solver plus pruning.  It is high upside but currently lacks the needed
factor-extraction theorem.

## P3: structured interpolation and constants

Two constrained-kernel objectives are worth retaining as secondary work:

* minimize the weighted degree of the separant to maximize the
  `q^e-Delta` root margin;
* penalize concentration in a single differential principal ideal, as a
  concrete precursor to the quotient-rank program.

By contrast, increasing `c`, changing floors, or recovering another factor
two is low priority: the exact sweep shows `c=32` is already close to its
limit, while the certificate deficits range from one order of magnitude to
many orders of magnitude.

## Revised execution order

| Priority | Deliverable | Success criterion |
|---|---|---|
| Done | P0.1 Lean root refinement | proved, including expansion-point amortization; green trust audit |
| Done | P0.2 one-variable adaptive evaluator | exact counts with independent exhaustive cross-checks |
| Done | P0.3 certified finite search | sharpened support witness at `d=49`; paper expression at `d=48` |
| Active | P0.4 unconditional quadratic family | kernel-check the finite integer inequality and prove the comparison uniformly |
| Highest | P0.5 executable `SOLVE` | replace extensional charging by checked execution semantics |
| P1.1 | Paper `K_r` direct-sum proof | closes the exact local rank and recovers `d=48` |
| P1.2 | Rectangle saddle-point theorem | removes or sharply reduces the `d^2/2` residue loss |
| P2.1 | Quotient-rank/multiple-`Q` lemma | excludes common-principal-ideal degeneracy |
| P2.2 | Linear-factor extraction | enables the fast affine-space solvers |
| P3 | Floor and constant tuning | only after a P1/P2 structural gain |

## Literature checkpoints

* [Kopparty, *List-Decoding Multiplicity Codes*](https://theoryofcomputing.org/articles/v011a005/),
  especially Theorem 4.4, Corollary 4.5, and `SOLVE`.
* [Brakensiek--Chen--Putterman--Zhang--Zheng, ECCC TR26-164](https://eccc.weizmann.ac.il/report/2026/164/),
  the source of the hidden-derivative interpolation and local-rank map.
* [Goyal--Harsha--Kumar--Shankar, fast list decoding](https://arxiv.org/abs/2311.17841),
  for nearly-linear solution of linear differential equations.
* [Goyal--Harsha--Kumar--Shankar, fast list recovery](https://arxiv.org/abs/2512.00248),
  which states the affine-space output and explicit `m^4` solver dependence.
* [Kumar, *Advances in List Decoding of Polynomial Codes*](https://arxiv.org/abs/2603.03841),
  for the current broader landscape and remaining RS questions.
