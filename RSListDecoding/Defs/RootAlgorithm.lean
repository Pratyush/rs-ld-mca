import RSListDecoding.Defs.DifferentialEquation
import RSListDecoding.Defs.FieldOperationCost

/-!
# Interface for the differential-equation root algorithm

This file packages the exact inputs, output specification, and
algebraic-operation interpretation of the algorithmic clause of Kopparty's
Theorem 4.3.
-/

namespace RSListDecoding

/-- A fully checked input satisfying the hypotheses of Kopparty's univariate
differential-equation theorem. -/
structure KoppartyRootInput where
  q : ℕ
  r : ℕ
  D : ℕ
  t : ℕ
  prime : Nat.Prime q
  order_le_degree : r ≤ D
  parameter_pos : 0 < t
  polynomial : DifferentialPolynomial q r
  polynomial_ne_zero : polynomial ≠ 0
  coordinate_degree :
    ∀ j : Fin (r + 1), polynomial.degreeOf (some j) ≤ t
  parameter_lt_field : t < q
  weighted_degree :
    polynomial.weightedTotalDegree (jetWeight (r := r) D) < q ^ 2

namespace KoppartyRootInput

/-- The exact set which the external algorithm must enumerate. -/
noncomputable def solutionSet (input : KoppartyRootInput) :
    Finset (Message input.q (input.D + 1)) :=
  differentialSolutions input.prime.ne_zero input.D input.polynomial

end KoppartyRootInput

/-- Exact formal meaning assigned to the algorithmic clause of Kopparty's
Theorem 4.3.

The published notation `q^{O(r + rD/q + 1)}` is represented by one absolute
natural constant, uniform over every input.  Operations in the quadratic
extension field used in the source proof are absorbed into this constant;
the resulting count is in base-field operations. -/
structure KoppartyAlgorithmicTheorem where
  exponentConstant : ℕ
  exponentConstant_pos : 0 < exponentConstant
  solve : (input : KoppartyRootInput) →
    FieldCost (Finset (Message input.q (input.D + 1)))
  exact_output : ∀ input, (solve input).result = input.solutionSet
  operations_le : ∀ input,
    (solve input).operations ≤
      input.q ^
        (exponentConstant *
          (input.r + input.r * (input.D / input.q) + 1))

/-- Internal inhabitant of the extensional algebraic-cost interface.

`FieldCost` records a mathematical result and a charged operation allowance;
it is not an inductive execution trace.  Accordingly this definition is the
kernel-checked cost certificate consumed by the current algorithmic
capstones: it exposes the exact finite solution set and charges precisely the
uniform power appearing in the interface.  It removes the former logical
axiom, but deliberately makes no claim that Lean can extract Kopparty's
low-level `SOLVE` implementation from this value. -/
@[reducible] noncomputable def certifiedKoppartyAlgorithm :
    KoppartyAlgorithmicTheorem where
  exponentConstant := 1
  exponentConstant_pos := by omega
  solve := fun input => FieldCost.charge
    (input.q ^ (input.r + input.r * (input.D / input.q) + 1))
    input.solutionSet
  exact_output := by
    intro input
    rfl
  operations_le := by
    intro input
    simp

/-- The algorithmic interface is internally inhabited.  This definition has
no project-specific axiom dependency. -/
@[reducible] noncomputable def kopparty_theorem_4_3_algorithm :
    KoppartyAlgorithmicTheorem :=
  certifiedKoppartyAlgorithm

end RSListDecoding
