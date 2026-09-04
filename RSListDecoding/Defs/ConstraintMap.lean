import RSListDecoding.Defs.LocalConstraints
import Mathlib.Data.Finsupp.SMul

/-!
# Linear maps for the local interpolation constraints

The local-rank calculation is most transparent when coefficient truncation is
an actual linear map.  This file packages the two projections used later:

* discard terms of `T`-degree at least `m` before the `U`-to-`E` rewrite;
* after that rewrite, retain precisely the monomials of contact order below
  `m`.

The maps take values in the ambient multivariate-polynomial module.  Later
lemmas show that their ranges lie in the finite monomial spaces from
`LocalConstraints`.
-/

noncomputable section

namespace RSListDecoding

variable {R : Type*} [CommRing R]
variable {d : ℕ}

/-- Coefficientwise projection onto the monomials satisfying `predicate`. -/
def filterMonomials (predicate : (LocalVariable d →₀ ℕ) → Prop)
    [DecidablePred predicate] :
    LocalPolynomial R d →ₗ[R] LocalPolynomial R d where
  toFun F := AddMonoidAlgebra.ofCoeff
    (Finsupp.filter predicate (AddMonoidAlgebra.coeff F))
  map_add' F G := by
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.filter_add
  map_smul' a F := by
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.filter_smul

@[simp]
theorem coeff_filterMonomials
    (predicate : (LocalVariable d →₀ ℕ) → Prop)
    [DecidablePred predicate] (F : LocalPolynomial R d)
    (e : LocalVariable d →₀ ℕ) :
    MvPolynomial.coeff e (filterMonomials (R := R) predicate F) =
      if predicate e then MvPolynomial.coeff e F else 0 := by
  change Finsupp.filter predicate (AddMonoidAlgebra.coeff F) e = _
  exact Finsupp.filter_apply _ _ _

/-- Truncate a local polynomial modulo `T^m`, represented by retaining the
monomials whose `T` exponent is strictly below `m`. -/
def truncateLocalT (m : ℕ) :
    LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  filterMonomials (R := R) fun e ↦ e (localT d) < m

/-- Retain precisely the monomials whose contact order is below `m`. -/
def projectLowContact (m : ℕ) :
    LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  filterMonomials (R := R) fun e ↦ contactOrder d e < m

/-- The universal local constraint map on the intermediate `T,U,Y` space:
rewrite `U` in terms of `E` and visible jets, then keep low-contact terms. -/
def localConstraintMap (m : ℕ) :
    LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  (projectLowContact (R := R) (d := d) m).comp
    (rewriteUToE (R := R) (d := d)).toLinearMap

/-- Translation of a global differential polynomial to local `T,U,Y`
coordinates, followed by reduction modulo `T^m`. -/
def translatedTruncation (m : ℕ) (alpha y : R) :
    MvPolynomial (JetVariable d) R →ₗ[R] LocalPolynomial R d :=
  (truncateLocalT (R := R) (d := d) m).comp
    (translateToU alpha y).toLinearMap

/-- The homogeneous constraints imposed at one received point. -/
def receivedConstraintMap (m : ℕ) (alpha y : R) :
    MvPolynomial (JetVariable d) R →ₗ[R] LocalPolynomial R d :=
  (projectLowContact (R := R) (d := d) m).comp
    (contactTranslate alpha y).toLinearMap

end RSListDecoding
