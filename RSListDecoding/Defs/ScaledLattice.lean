import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Scaled exponent lattices

The hidden-derivative interpolation argument indexes jet monomials by
`d - 1` nonnegative exponents.  Coordinate `i` has anisotropic cost
`i + 1`.  This file keeps that combinatorics independent of polynomial and
linear-algebra infrastructure.
-/

namespace RSListDecoding

open scoped BigOperators

/-- A tuple of the `d - 1` nonconstant jet exponents. -/
abbrev ScaledExponent (d : ℕ) := Fin (d - 1) → ℕ

/-- An ordinary discrete simplex, represented by a nonnegative tuple whose
coordinate sum is bounded by `z`. -/
def OrdinarySimplex (r z : ℕ) :=
  {a : Fin r → ℕ // ∑ i, a i ≤ z}

/-- The coordinatewise remainder box for division by the scaled weights.
Its cardinality is `(d - 1)!`. -/
abbrev ScaledResidue (d : ℕ) :=
  (i : Fin (d - 1)) → Fin (i.val + 1)

/-- Total maximum coordinatewise remainder in `ScaledResidue d`. -/
def scaledRemainderSlack (d : ℕ) : ℕ :=
  ∑ i : Fin (d - 1), i.val

/-- The ordinary total degree of a jet-exponent tuple. -/
def scaledOrdinaryDegree {d : ℕ} (c : ScaledExponent d) : ℕ :=
  ∑ i, c i

/-- The anisotropic weight `Σᵢ (i+1)cᵢ`. -/
def scaledWeight {d : ℕ} (c : ScaledExponent d) : ℕ :=
  ∑ i, (i.val + 1) * c i

/-- A finite ambient box containing every tuple of scaled weight at most
`z`. -/
def scaledExponentBox (d z : ℕ) : Finset (ScaledExponent d) :=
  Fintype.piFinset fun _ : Fin (d - 1) ↦ Finset.range (z + 1)

/-- The finite anisotropic simplex of tuples having scaled weight at most
`z`. -/
def scaledExponentFinset (d z : ℕ) : Finset (ScaledExponent d) :=
  (scaledExponentBox d z).filter fun c ↦ scaledWeight c ≤ z

/-- The part of the anisotropic simplex that also has ordinary degree at
most `S`.  This is the finite set used by the repaired shell argument. -/
def goodScaledExponentFinset (d z S : ℕ) : Finset (ScaledExponent d) :=
  (scaledExponentFinset d z).filter fun c ↦ scaledOrdinaryDegree c ≤ S

/-- Bundled lattice points of scaled weight at most `z`. -/
abbrev BoundedScaledExponent (d z : ℕ) :=
  ↥(scaledExponentFinset d z)

/-- Bundled points satisfying both cutoffs. -/
abbrev GoodScaledExponent (d z S : ℕ) :=
  ↥(goodScaledExponentFinset d z S)

/-- Number of lattice points in the anisotropic simplex. -/
def scaledExponentCount (d z : ℕ) : ℕ :=
  (scaledExponentFinset d z).card

/-- Number of points satisfying both the scaled and ordinary degree
budgets. -/
def goodScaledExponentCount (d z S : ℕ) : ℕ :=
  (goodScaledExponentFinset d z S).card

end RSListDecoding
