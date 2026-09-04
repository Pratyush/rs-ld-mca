import RSListDecoding.Defs.HasseDerivative
import RSListDecoding.Defs.ReedSolomon
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomial differential equations

This module gives the exact algebraic objects used at the one external trust
boundary in the combinatorial proof.  A variable is either `none`, denoting
the independent variable `X`, or `some j`, denoting the jet variable `Y_j`.
Specialization sends `Y_j` to the `j`-th Hasse derivative of a candidate
univariate polynomial.
-/

noncomputable section

namespace RSListDecoding

/-- Variables `X, Y₀, ..., Yᵣ` of an order-`r` polynomial differential
equation.  `none` denotes `X`, while `some j` denotes `Y_j`. -/
abbrev JetVariable (r : ℕ) := Option (Fin (r + 1))

/-- A polynomial in `X, Y₀, ..., Yᵣ` over `ZMod q`. -/
abbrev DifferentialPolynomial (q r : ℕ) :=
  MvPolynomial (JetVariable r) (ZMod q)

/-- The weight vector `(1, D, D-1, ..., D-r)` from Kopparty's differential
equation theorem. -/
def jetWeight {r : ℕ} (D : ℕ) : JetVariable r → ℕ
  | none => 1
  | some j => D - (j : ℕ)

/-- The polynomial with coefficient vector `p`.  A vector of length `D+1`
represents exactly a polynomial of degree at most `D`. -/
def messagePolynomial {q D : ℕ} (p : Message q (D + 1)) : Polynomial (ZMod q) :=
  ↑((Polynomial.degreeLTEquiv (ZMod q) (D + 1)).symm p)

/-- Substitute `X ↦ X` and `Y_j ↦ P⁽ʲ⁾` into a polynomial differential
equation, where `P⁽ʲ⁾` is the `j`-th Hasse derivative. -/
def differentialSpecialization {q r : ℕ} (Q : DifferentialPolynomial q r)
    (P : Polynomial (ZMod q)) : Polynomial (ZMod q) :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun v => match v with
      | none => Polynomial.X
      | some j => hasseDerivative (j : ℕ) P) Q

/-- Coefficient vectors of degree-at-most-`D` polynomial solutions of `Q`.
The witness `q ≠ 0` supplies the finite instance for `ZMod q`. -/
def differentialSolutions {q r : ℕ} (hq : q ≠ 0) (D : ℕ)
    (Q : DifferentialPolynomial q r) : Finset (Message q (D + 1)) := by
  letI : NeZero q := ⟨hq⟩
  exact Finset.univ.filter fun p =>
    differentialSpecialization Q (messagePolynomial p) = 0

end RSListDecoding
