import RSListDecoding.Defs.DifferentialEquation
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Local hidden-derivative constraints

This module encodes the two local changes of variables used by the
interpolation argument.  A local variable is either `T`, the auxiliary
variable `U` (or, after the second change of variables, `E`), or one of the
visible jet variables `Y₁, ..., Y_d`.

The definitions deliberately separate the substitutions

* `X = alpha + T`, `Y₀ = y + T U`, and
* `U = E + sum_j (-1)^(j+1) T^(j-1) Y_j`.

This makes the intermediate space `V` and the final contact-coefficient map
available independently for the local-rank proof.
-/

noncomputable section

open scoped BigOperators

namespace RSListDecoding

open MvPolynomial

/-- Variables in a local expansion.  `none` denotes `T`, `some none` denotes
the auxiliary variable (`U` before rewriting and `E` afterwards), and
`some (some j)` denotes the paper variable `Y_{j+1}`. -/
abbrev LocalVariable (d : ℕ) := Option (Option (Fin d))

/-- Polynomials in `T`, one auxiliary variable, and `Y₁, ..., Y_d`. -/
abbrev LocalPolynomial (R : Type*) [CommSemiring R] (d : ℕ) :=
  MvPolynomial (LocalVariable d) R

/-- The local displacement variable `T`. -/
def localT (d : ℕ) : LocalVariable d := none

/-- The shared variable slot interpreted as `U` before the contact rewrite. -/
def localU (d : ℕ) : LocalVariable d := some none

/-- The shared variable slot interpreted as `E` after the contact rewrite. -/
def localE (d : ℕ) : LocalVariable d := some none

/-- The local variable representing the paper variable `Y_{j+1}`. -/
def localY {d : ℕ} (j : Fin d) : LocalVariable d := some (some j)

variable {R : Type*} [CommRing R]
variable {d : ℕ}

/-- First local change of variables:
`X ↦ alpha + T`, `Y₀ ↦ y + T U`, and `Y_{j+1} ↦ Y_{j+1}`.

Using `Fin.cases` for the jet index keeps the `Y₀`/positive-order split
definitionally aligned with `JetVariable d = Option (Fin (d+1))`. -/
def translateToU (alpha y : R) :
    MvPolynomial (JetVariable d) R →ₐ[R] LocalPolynomial R d :=
  MvPolynomial.bind₁ fun v =>
    match v with
    | none => C alpha + X (localT d)
    | some j =>
        Fin.cases
          (C y + X (localT d) * X (localU d))
          (fun i => X (localY i)) j

/-- The signed summand attached to `Y_{j+1}` in the local formula for `U`:
`(-1)^(j+2) T^j Y_{j+1}`.

Thus zero-based `j` corresponds to paper index `ell = j+1`, and the sign is
`(-1)^(ell+1)` as in the backward Hasse--Taylor identity. -/
def localJetTerm (j : Fin d) : LocalPolynomial R d :=
  C ((-1 : R) ^ ((j : ℕ) + 2)) *
    X (localT d) ^ (j : ℕ) * X (localY j)

/-- The visible-jet part of `U = E + sum_j (-1)^(j+1) T^(j-1) Y_j`. -/
def localJetSum : LocalPolynomial R d :=
  ∑ j : Fin d, localJetTerm (R := R) j

/-- Second local change of variables:
`U ↦ E + sum_j (-1)^(j+1) T^(j-1) Y_j`, fixing `T` and every `Y_j`.

The source and target variable types coincide; `localU` and `localE` name
the same slot but document its interpretation on the two sides. -/
def rewriteUToE : LocalPolynomial R d →ₐ[R] LocalPolynomial R d :=
  MvPolynomial.bind₁ fun v =>
    match v with
    | none => X (localT d)
    | some none => X (localE d) + localJetSum (R := R) (d := d)
    | some (some j) => X (localY j)

/-- The complete local expansion from `X,Y₀,...,Y_d` to
`T,E,Y₁,...,Y_d`. -/
def contactTranslate (alpha y : R) :
    MvPolynomial (JetVariable d) R →ₐ[R] LocalPolynomial R d :=
  (rewriteUToE (R := R) (d := d)).comp (translateToU alpha y)

/-- Contact weights: `T` has weight one, `E` has weight `d`, and visible
jet variables have weight zero. -/
def contactWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 1
  | some none => d
  | some (some _) => 0

/-- The contact order of a local monomial exponent.  For
`T^i E^b Y^e`, this is `i + d*b`. -/
def contactOrder (d : ℕ) (e : LocalVariable d →₀ ℕ) : ℕ :=
  e.sum fun v exponent => contactWeight d v * exponent

/-- Exponent vectors of contact order strictly below `m`; these are exactly
the coefficients required to vanish by the local divisibility condition. -/
def LowContactIndex (d m : ℕ) :=
  {e : LocalVariable d →₀ ℕ // contactOrder d e < m}

/-- Simultaneous extraction of all coefficients whose contact order is below
`m`.  This is the linear map underlying the imposed local constraints. -/
def lowContactCoefficients (m : ℕ) :
    LocalPolynomial R d →ₗ[R] (LowContactIndex d m → R) :=
  LinearMap.pi fun (e : LowContactIndex d m) => MvPolynomial.lcoeff R e.1

/-- A global differential polynomial satisfies the manuscript's local
constraints of multiplicity `m` at `(alpha,y)` exactly when every translated
coefficient of contact order below `m` is zero. -/
def SatisfiesLocalConstraints (m : ℕ) (alpha y : R)
    (Q : MvPolynomial (JetVariable d) R) : Prop :=
  lowContactCoefficients (R := R) (d := d) m (contactTranslate alpha y Q) = 0

/-- Exponent of the visible first jet `Y₁`.  The support-sum formulation is
total even when `d = 0`; in the intended range `d > 0` it is simply the
coefficient at `localY 0`. -/
def localFirstJetExponent (e : LocalVariable d →₀ ℕ) : ℕ :=
  e.sum fun v exponent =>
    match v with
    | some (some j) => if (j : ℕ) = 0 then exponent else 0
    | _ => 0

/-- The anisotropic exponent weight on visible jets: paper variable `Y_j`
has weight `j-1`.  In zero-based local indexing, `localY j` therefore has
weight `j`. -/
def localAnisotropicWeight (e : LocalVariable d →₀ ℕ) : ℕ :=
  e.sum fun v exponent =>
    match v with
    | some (some j) => (j : ℕ) * exponent
    | _ => 0

/-- Exponent predicate defining the intermediate space `V` from the local
rank argument. -/
def VExponent (m W : ℕ) (e : LocalVariable d →₀ ℕ) : Prop :=
  e (localT d) < m ∧
    e (localU d) ≤ e (localT d) ∧
    localFirstJetExponent e ≤ m ∧
    localAnisotropicWeight e ≤ W + e (localT d)

/-- Exponent predicate defining the contact-envelope space `W` from the
local rank argument. -/
def ContactEnvelopeExponent (m W : ℕ) (e : LocalVariable d →₀ ℕ) : Prop :=
  contactOrder d e < m ∧
    localFirstJetExponent e ≤ 2 * m - 1 ∧
    localAnisotropicWeight e ≤ W + m - 1

/-- Contact-layer-adaptive envelope.  Both visible-jet allowances retain the
actual low-contact coordinates instead of replacing them by their common
worst-case value `m-1`. -/
def CoupledContactEnvelopeExponent (m W : ℕ)
    (e : LocalVariable d →₀ ℕ) : Prop :=
  contactOrder d e < m ∧
    localFirstJetExponent e ≤ m + e (localT d) ∧
    localAnisotropicWeight e ≤ W + contactOrder d e

/-- Support envelope retaining the two signed invariants of the `U`-to-`E`
rewrite.  An output monomial has `E` exponent at most its `T` exponent, and
its higher-jet anisotropic weight is bounded by `W` plus that same `T`
exponent.  These are stronger than the corresponding clauses of
`CoupledContactEnvelopeExponent`. -/
def SharpenedContactEnvelopeExponent (m W : ℕ)
    (e : LocalVariable d →₀ ℕ) : Prop :=
  contactOrder d e < m ∧
    e (localE d) ≤ e (localT d) ∧
    localFirstJetExponent e ≤ m + e (localT d) ∧
    localAnisotropicWeight e ≤ W + e (localT d)

/-- The canonical monomial submodule selected by an exponent predicate.
Using `restrictSupport` exposes Mathlib's restricted monomial basis directly
for the later rank computation. -/
def localExponentSpan (predicate : (LocalVariable d →₀ ℕ) → Prop) :
    Submodule R (LocalPolynomial R d) :=
  MvPolynomial.restrictSupport R {e | predicate e}

/-- The manuscript's intermediate local space `V`. -/
def localVSpace (m W : ℕ) : Submodule R (LocalPolynomial R d) :=
  localExponentSpan (R := R) (VExponent (d := d) m W)

/-- The contact-envelope space containing precisely the allowed low-contact
monomial shapes used as the codomain of the local constraint map. -/
def contactEnvelopeSpace (m W : ℕ) : Submodule R (LocalPolynomial R d) :=
  localExponentSpan (R := R) (ContactEnvelopeExponent (d := d) m W)

/-- The smaller, contact-layer-adaptive codomain for the local constraint
map. -/
def coupledContactEnvelopeSpace (m W : ℕ) :
    Submodule R (LocalPolynomial R d) :=
  localExponentSpan (R := R)
    (CoupledContactEnvelopeExponent (d := d) m W)

/-- The sharpened support codomain for the universal local constraint map. -/
def sharpenedContactEnvelopeSpace (m W : ℕ) :
    Submodule R (LocalPolynomial R d) :=
  localExponentSpan (R := R)
    (SharpenedContactEnvelopeExponent (d := d) m W)

end RSListDecoding
