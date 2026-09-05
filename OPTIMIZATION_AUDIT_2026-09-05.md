# Optimization audit: exact rank, multiple interpolants, and saddle point

This report records the results of the three follow-up investigations.  The
checked-in `ld.pdf` is the original low-rate version.  ECCC Revision 1 now
contains a separate all-rate padding reduction:

<https://eccc.weizmann.ac.il/report/2026/164/revision/1/download>

## 1. Exact paper local rank

For `0 <= r < m`, put

```text
h_r = ceil((m-r)/d),
B_r = (r+1)(m+1) - (r+1-h_r)_+ (m+1-h_r)_+.
```

The exact manuscript bound is

```text
paperLocalRankCount(d,m,W) = sum_{r<m} B_r N_d(W+r).
```

The Lean source now contains executable definitions of `paperKernelHeight`,
`paperLocalRankCoefficient`, and `paperLocalRankCount`.  The Python evaluator
computes the same sum.  A separate dense finite-field experiment constructs
the universal map `Gamma : V -> low-contact coefficients` and computes its
rank.  On all 72 cases

```text
q in {5,7}, d in {1,2,3}, m in {1,2,3,4}, W in {0,1,2},
```

the measured rank equals (not merely lies below) `paperLocalRankCount`.

The remaining proof obligation is precise: formalize the independent direct
sum of manuscript kernel spaces `K_r`.  It requires proving that the leading
`T^r` coefficient `(U-Y_1)^h g` cannot cancel between layers.  Until this is
proved, `paperLocalRankCount` is executable data and experimentally checked,
but is not used by a Lean capstone.

### Fully proved support-only substitute

The rewrite preserves two stronger support invariants:

```text
E-degree <= T-degree,
higher-jet weight <= W + T-degree.
```

Lean now proves that the local map lands in the resulting sharpened envelope,
computes its finite cardinality, compares its dimension with the adaptive
global space, and exports combinatorial and amortized list-decoding theorems.
Its exact count is

```text
sum_{t<m}
  (min(floor((m-1-t)/d),t)+1) (m+t+1) N_d(W+t).
```

This is slightly weaker than the paper quotient but already gives a passing
finite witness:

| method | d | m | W | C | q | `G/(nL)` |
|---|---:|---:|---:|---:|---:|---:|
| paper quotient (evaluator only) | 48 | 73,728 | 1,453,006 | 147,456 | 223,207 | 1.004487 |
| sharpened support (Lean theorem) | 49 | 76,832 | 1,539,209 | 153,664 | 232,607 | 1.011276 |
| paper quotient (comparison) | 49 | 76,832 | 1,539,209 | 153,664 | 232,607 | 1.018508 |

The common parameters are `n=100000`, `A=99900`, `K=33000`, `c=32`, and
`a=2`.  The sharpened result therefore loses only one derivative order to the
unformalized paper quotient.

## 2. Full interpolation kernel / several equations

`scripts/full_kernel_experiment.py` now constructs the entire interpolation
matrix over a small prime field, finds a nullspace basis, specializes every
basis interpolant at every degree-`<K` message, and compares:

```text
zeros of one basis interpolant,
zeros of every basis interpolant,
actual agreement candidates.
```

Two exhaustive `q=5,n=4` received-word sweeps covered 1,250 received words.
There was no instance in which the common zero set was smaller than the zero
set of the best nullspace-basis element.  In 100 cases some *other* basis
element had unnecessary roots, so using more equations can repair a poor
choice of `Q`; it did not beat a good single choice in these tests.

This is negative evidence, not an impossibility theorem.  It lowers the
priority of generic “use all of the kernel.”  The version still worth proving
is quotient rank: show that the interpolation kernel has large image modulo
every low-weight differential principal ideal.  That would rule out the
shared-factor obstruction seen in worst-case examples.

## 3. Gaussian-rectangle saddle point

The exact good shell is the number of partitions in a `C` by `d-1`
rectangle.  `scripts/saddle_point_experiment.py` compares its exact
coefficients with the canonical independent-geometric tilt.  For

```text
m = c d^2, C = a m, W = floor(a d m/(1+log d)),
```

the saddle satisfies, to first order,

```text
tau ~ (1+log d)/(a m).
```

Conditioning the number of parts on total weight predicts

```text
z -> sqrt(6) (1-EulerGamma) / pi,
rho := Pr(height <= C | weight=W) -> Phi(z) ~= 0.629.
```

It consequently predicts the sharper shell ratio

```text
N_d(W+m) / goodRectangle(d,W,C)
  ~ (exp(1/a)/rho) d^(1/a).
```

For `c=32,a=2`, the predicted normalized constant is about `2.62`.  Exact
values at `d=6,8,10,12,16,20,24,32` rise from `1.485` to `1.974`; the exact
weight cap fractions range from `0.591` to `0.683`, while the normal
prediction ranges from `0.526` to `0.612`.  Convergence is slow but the trend
is consistent with the formula.

What remains is a uniform two-dimensional local central limit theorem for
the triangular array of independent geometric variables, plus a bound that
passes from one weight to the cumulative shell.  The numerical work identifies
the expected constant and scaling; it is not yet a proof usable by Lean.

## Padding versus the direct all-rate proof

The revised paper chooses a tiny low-rate agreement `eta`, enlarges the
message dimension to

```text
k' = max(k, ceil(eta^(-3/theta))+1),
```

and pads to

```text
N = max(n, ceil(k'/((1-theta)eta))).
```

It extends the evaluation set inside the same field, pads the received word
with zeros, invokes the low-rate decoder, and prunes against the original
coordinates.  `Padding.lean` proves the underlying monotonicity at the same
absolute agreement threshold; the new coordinate values may in fact be
arbitrary, not necessarily zero.

The reduction is the preferred asymptotic proof: it is short, modular, and
inherits future improvements to the low-rate decoder.  It does, however,
require enough unused field points (`q >= N`) and therefore does not preserve
full-length `n=q` codes.  The branch's direct free-order proof runs on the
original coordinates, permits `q=n` once its other finite hypotheses hold,
and has much better concrete parameters, at the price of substantially more
rank analysis.

The published constants make the distinction extreme.  At target rate
`R=.33` and agreement `.999`, the paper's fixed choice has
`theta=.334835` and optimistically `eta` below roughly `10^-35.995`.  The
auxiliary `k'` is then already on the scale `10^322.5`, and `N` on the scale
`10^358.7` until the original block length is itself enormous.  In contrast,
the direct sharpened finite witness above has `n=100000`, `d=49`, and
`q=232607`.  This does not make the decoder practical: the amortized proved
list cap is about `q^99.012`, or `2^1765`, and the current coarse algorithmic
envelope at order 49 is `q^(35*50)` (about `2^31198` operations).  It only
shows that direct interpolation is many orders of magnitude closer to a
meaningful finite theorem.

## Revised priorities

1. **Executable `SOLVE` trace.**  This remains the largest rigor gap between
   the algorithmic theorem and an extractable decoder.
2. **Paper `K_r` direct-sum proof.**  It recovers the `d=48` witness and closes
   the last one-order local-rank gap.  It is now a sharply bounded Lean task.
3. **Rectangle local CLT.**  This is the only current direction likely to
   reduce the multiplicity exponent or materially improve broad parameter
   regimes.
4. **Quotient-rank theorem for multiple `Q`.**  Continue only with a statement
   excluding common differential factors; raw common-root experiments do not
   justify higher priority.
5. **Constants and floors.**  Defer until one of the structural items above
   lands.

## Reproduction

```bash
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/local_rank_experiment.py --q 7 --d 3 --m 4 --W 2
python3 scripts/full_kernel_sweep.py \
  --q 5 --d 2 --m 2 --W 1 --C 2 --n 4 --A 3 --K 2 --B 2 \
  --alphas 0,1,2,3
python3 scripts/saddle_point_experiment.py \
  --d 6 8 10 12 16 20 24 32 --c 32 --a 2
python3 scripts/scan_quadratic_parameters.py \
  --rate 33/100 --agreement 999/1000 --n 100000 \
  --d 49:49 --c 32 --a 2 --criterion sharpened --passing-only
```
