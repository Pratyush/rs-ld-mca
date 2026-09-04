import Mathlib.Algebra.Polynomial.Taylor

/-!
# Hasse derivatives

This module fixes the Hasse-derivative convention used in the manuscript.
We deliberately reuse Mathlib's characteristic-safe implementation rather
than define the same coefficient transformation a second time.
-/

noncomputable section

namespace RSListDecoding

/-- The `ell`-th Hasse derivative of a univariate polynomial.

The coefficient of `X ^ n` in `hasseDerivative ell P` is
`Nat.choose (n + ell) ell * P.coeff (n + ell)`.  Thus this is the divided-power
derivative used in the manuscript, including in positive characteristic. -/
abbrev hasseDerivative {R : Type*} [Semiring R] (ell : ℕ)
    (P : Polynomial R) : Polynomial R :=
  Polynomial.hasseDeriv ell P

/-- Evaluation of the `ell`-th Hasse derivative at `x`. -/
def hasseDerivativeAt {R : Type*} [Semiring R] (ell : ℕ)
    (P : Polynomial R) (x : R) : R :=
  (hasseDerivative ell P).eval x

end RSListDecoding

