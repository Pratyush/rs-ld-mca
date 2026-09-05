# Degree-below-characteristic differential root count

This note supplies the proof of the root-count refinement used by
`RSListDecoding/Lemmas/RootCount.lean`.  It is a refinement of the proof of
Kopparty's Theorem 4.3, not the literal displayed statement of that theorem.

## Statement

Let `q` be prime, let `E = F_{q^e}` with `e > 0`, and let

```text
Q(X,Y_0,...,Y_r) in F_q[X,Y_0,...,Y_r]
```

be nonzero.  Give `X,Y_0,...,Y_r` weights `1,D,D-1,...,D-r`.
Assume

1. `r <= D < q`;
2. `0 < t < q` and `deg_{Y_j}(Q) <= t` for every `j`;
3. the weighted degree of `Q` is less than `q^e`.

Then the number of `P in F_q[T]` of degree at most `D` satisfying

```text
Q(T,P(T),P^(1)(T),...,P^(r)(T)) = 0
```

where the superscripts denote Hasse derivatives, is at most

```text
t * sum_{j=0}^r q^(e*(j+1)).
```

The proof also gives the margin refinement

```text
(q^e - Delta) * #solutions
  <= t * sum_{j=0}^r q^(e*(j+1)),
```

if the weighted degree is at most `Delta < q^e`.

## 1. Degree and extension-field facts

Embed `F_q` in `E`.  Coefficient extension preserves nonzeroness and all
coordinate-degree bounds.

For a differential polynomial `G` whose weighted degree is at most `Delta`
and a polynomial `P` of degree at most `D`, put

```text
G[P](T) = G(T,P(T),P^(1)(T),...,P^(r)(T)).
```

Every substituted variable has degree at most its assigned weight, because
`deg P^(j) <= D-j`.  Consequently `deg G[P] <= Delta`.  Taking an ordinary
partial derivative in a jet variable cannot increase weighted degree.
Therefore, whenever `(partial_{Y_j} G)[P]` is nonzero, it is nonzero at at
least `q^e-Delta` points of `E`.

## 2. Uniqueness of a regular lift

Fix `alpha in E` and initial Hasse data
`beta_0,...,beta_j in E`.  Suppose

```text
partial_{Y_j} G(alpha,beta_0,...,beta_j) != 0.
```

Kopparty's Theorem 4.4 determines the coefficient of
`(T-alpha)^i`, for `i=j+1,...,D`, from the preceding coefficients whenever
`binom(i,j)` is nonzero in `E`.  Here `0 <= j < i <= D < q`.  Since `q` is
prime, all factorials occurring in

```text
binom(i,j) = i! / (j! (i-j)!)
```

are nonzero modulo `q`; hence every such binomial coefficient is nonzero.
It follows inductively that at most one degree-at-most-`D` solution has the
given regular initial data.  This is the exact place where `D < q` removes
the `|E|^(j*floor(D/q)+j)` branching term in Corollary 4.5.

## 3. Multiplicity strata cost `t`, not `t+1`

Run Kopparty's `SOLVE` recursion, but group its nodes by their current highest
jet variable.  At a node with highest variable `Y_j`, recursive calls replace
the current polynomial by successive ordinary derivatives in `Y_j` until it
no longer depends on `Y_j`; the recursion then moves to a lower jet.

Fix `alpha,beta_0,...,beta_{j-1}`.  Regard the current polynomial as the
univariate polynomial

```text
g(Z) = G(alpha,beta_0,...,beta_{j-1},Z).
```

The regular branch after `ell` recursive derivatives consists of those
`z in E` for which

```text
g(z)=g'(z)=...=g^(ell)(z)=0,  g^(ell+1)(z) != 0.
```

These sets are disjoint as `ell` varies.  A root of multiplicity `mu`
appears in exactly one stratum and contributes one value of `z`, while the
sum of all root multiplicities is at most `deg g`.  Thus the total number of
regular `z` values over all strata is at most
`deg_{Y_j} G <= t`.  The assumption `t < q` also ensures that the ordinary
derivative chain detects multiplicity correctly in characteristic `q`.

There are `|E|^(j+1) = q^(e*(j+1))` choices of
`alpha,beta_0,...,beta_{j-1}`.  By regular-lift uniqueness, all regular
branches whose highest variable is `Y_j` therefore produce at most

```text
t * q^(e*(j+1))
```

distinct solutions.  This count already includes the expansion point
`alpha`; no field-size factor has been discarded.

## 4. Coverage and summation

Take any solution `P`.  Follow it down the `SOLVE` derivative recursion.
The recursion cannot differentiate forever: coordinate degree is less than
`q`, so a nonconstant polynomial in the current highest jet has a nonzero
next derivative, and after at most its coordinate degree many steps that jet
disappears.  Since `Q` is nonzero, the process eventually reaches a pair
`(G,Y_j)` for which

```text
H(T) = (partial_{Y_j} G)[P](T)
```

is a nonzero polynomial.  Its degree is less than `q^e`, so some
`alpha in E` has `H(alpha) != 0`.  At that expansion point, `P` lies in the
regular branch counted in Section 3.  Hence every solution is covered.

Summing the Section 3 bound over `j=0,...,r` proves

```text
#solutions <= t * sum_{j=0}^r q^(e*(j+1)).
```

Counting pairs `(P,alpha)` instead proves the stronger margin statement:
for the first recursion node at which the displayed `H` is nonzero, each
`P` has at least `q^e-Delta` regular choices of `alpha`, whereas the same
fiber count bounds all regular pairs by the right-hand side.

## 5. Checks against the implementation

* `degree <= D` is represented by a coefficient vector of length `D+1`.
* The highest-jet fiber has degree at most `t`, so the coefficient is `t`,
  not `t+1`.
* The extension is used only to find a nonvanishing expansion point.  The
  output is filtered back to polynomials over `F_q`, so extension-field
  duplicates can only reduce the final cardinality.
* Repeated roots are precisely what the derivative strata encode.
* Partial differentiation and Hasse specialization do not increase the
  weighted-degree budget.

## Trust boundary

The argument above is not the literal numeric conclusion printed in
Kopparty's Theorem 4.3; it is a specialization of its proof.  The current
Lean patch now uses Mathlib's `GaloisField q e` and proves scalar-extension
compatibility, preservation of nonzeroness and degree bounds, the
finite-field nonvanishing-point lemma, the degree-below-characteristic
regular-lift uniqueness theorem, and the exact `t`-sized regular fibre count.
It also proves characteristic-safe Hasse partial strata, the existence of a
regular stratum and expansion point whenever the top stratum specializes
nontrivially, and regular-lift uniqueness at an arbitrary expansion point.
The latter now works in the original ambient jet-variable type under a
checked active-order invariant.  Top Hasse extraction preserves support,
removes the active variable, and therefore lowers that invariant one order at
a time.  Finally, the refinement-key space has the claimed geometric-sum
cardinality.

The remaining connection is the finite recursive partition: split solutions
according to whether the current top stratum specializes to zero, send the
zero branch to the next lower active order, and count the regular branch by
its expansion point and lower Taylor jet.  Formalizing the associated choice
function and proving its fibres have total size at most `t` will connect the
compiled local lemmas into the global coverage/disjointness theorem.
`Assumptions.lean` therefore still records the final cardinality statement as
an external input.  That axiom must not be removed until this partition and
the final scalar-extension count compile; merely renaming it would not reduce
the trust boundary.

## Reference

Swastik Kopparty, “List-Decoding Multiplicity Codes,” *Theory of Computing*
11(5), 2015, Theorem 4.3 and its proof, especially Theorem 4.4,
Corollary 4.5, and `SOLVE`, pp. 163--167.
