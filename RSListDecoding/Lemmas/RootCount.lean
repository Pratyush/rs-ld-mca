import RSListDecoding.Lemmas.RootRefinement
import RSListDecoding.Lemmas.Parameters

/-!
# Cardinality bounds for polynomial differential equations

This module contains checked arithmetic specializations of the internally
proved root-counting theorem.  In the application the solution degree is `K-1 < q`.
The refined count therefore has exponent `2d+2` with the quadratic extension,
and exponent `d+1` whenever the weighted degree is already below `q`.
-/

namespace RSListDecoding

/-- The coefficient-vector encoding really lands in the source theorem's
degree-at-most-`D` solution space. -/
theorem messagePolynomial_degree_lt {q D : ℕ} (p : Message q (D + 1)) :
    (messagePolynomial p).degree < (D + 1 : ℕ) := by
  exact Polynomial.mem_degreeLT.mp
    ((Polynomial.degreeLTEquiv (ZMod q) (D + 1)).symm p).property

/-- Coefficient vectors give distinct candidate polynomials. -/
theorem messagePolynomial_injective {q D : ℕ} :
    Function.Injective (messagePolynomial : Message q (D + 1) → Polynomial (ZMod q)) := by
  intro p p' h
  apply (Polynomial.degreeLTEquiv (ZMod q) (D + 1)).symm.injective
  apply Subtype.ext
  exact h

/-- Membership in `differentialSolutions` is exactly satisfaction of the
specialized polynomial differential equation. -/
theorem mem_differentialSolutions {q r D : ℕ} (hq : q ≠ 0)
    (Q : DifferentialPolynomial q r) (p : Message q (D + 1)) :
    p ∈ differentialSolutions hq D Q ↔
      differentialSpecialization Q (messagePolynomial p) = 0 := by
  letI : NeZero q := ⟨hq⟩
  simp [differentialSolutions]

/-- Refined Kopparty cardinality bound using the quadratic extension when the
solution degree is smaller than the characteristic. -/
theorem kopparty_cardinality_of_degree_lt_field {q r D t : ℕ}
    (hq : Nat.Prime q) (hrD : r ≤ D) (ht : 0 < t)
    (Q : DifferentialPolynomial q r) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (r + 1), Q.degreeOf (some j) ≤ t)
    (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < q ^ 2)
    (hDq : D < q) :
    (differentialSolutions hq.ne_zero D Q).card ≤
      t * rootCountGeometricFactor q 2 r := by
  exact kopparty_degree_lt_characteristic_cardinality
    hq hrD hDq ht (by omega : 0 < 2) Q hQ hcoord htq hweight

/-- If the weighted degree is below the base-field size, the same refined
argument runs over `ZMod q` itself and pays only `q^(r+1)`. -/
theorem kopparty_cardinality_of_weight_lt_field {q r D t : ℕ}
    (hq : Nat.Prime q) (hrD : r ≤ D) (ht : 0 < t)
    (Q : DifferentialPolynomial q r) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (r + 1), Q.degreeOf (some j) ≤ t)
    (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < q)
    (hDq : D < q) :
    (differentialSolutions hq.ne_zero D Q).card ≤
      t * rootCountGeometricFactor q 1 r := by
  have hweight' :
      Q.weightedTotalDegree (jetWeight (r := r) D) < q ^ 1 := by
    simpa using hweight
  exact kopparty_degree_lt_characteristic_cardinality
    hq hrD hDq ht (by omega : 0 < 1) Q hQ hcoord htq hweight'

/-- The sharp internal bound used by the combinatorial proof.  Here the
solution polynomials have degree at most `K-1`, the derivative depth is `d`,
and the individual jet-variable degree cap is `B`. -/
theorem differentialSolutions_card_le_sharp {q d K B : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hB : 0 < B)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q) (hKq : K ≤ q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2) :
    (differentialSolutions hq.ne_zero (K - 1) Q).card ≤
      B * rootCountGeometricFactor q 2 d := by
  have hdD : d ≤ K - 1 := by omega
  have hDq : K - 1 < q := by omega
  exact kopparty_cardinality_of_degree_lt_field
    hq hdD hB Q hQ hcoord hBq hweight hDq

/-- Expansion-point-amortized sharp bound with an explicit weighted-degree
cap `Delta`. -/
theorem differentialSolutions_card_le_amortized
    {q d K B Delta : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hB : 0 < B)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q) (hKq : K ≤ q)
    (hweight : Q.weightedTotalDegree
      (jetWeight (r := d) (K - 1)) ≤ Delta)
    (hDelta : Delta < q ^ 2) :
    (differentialSolutions hq.ne_zero (K - 1) Q).card ≤
      (B * rootCountGeometricFactor q 2 d) / (q ^ 2 - Delta) := by
  have hdD : d ≤ K - 1 := by omega
  have hDq : K - 1 < q := by omega
  exact kopparty_degree_lt_characteristic_cardinality_div
    hq hdD hDq hB (by omega : 0 < 2) Q hQ hcoord hBq hweight hDelta

/-- Base-field version of the sharp internal bound. -/
theorem differentialSolutions_card_le_baseField {q d K B : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hB : 0 < B)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q) (hKq : K ≤ q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q) :
    (differentialSolutions hq.ne_zero (K - 1) Q).card ≤
      B * rootCountGeometricFactor q 1 d := by
  have hdD : d ≤ K - 1 := by omega
  have hDq : K - 1 < q := by omega
  exact kopparty_cardinality_of_weight_lt_field
    hq hdD hB Q hQ hcoord hBq hweight hDq

/-- The sharp differential-equation count fits into the public
`q^(2d+4)` list bound under the scope's ambient-dimension and field-size
hypotheses. -/
theorem differentialSolutions_card_le_public {q d K n B : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hKn : K < n) (hnq : n ≤ q)
    (hB : 0 < B)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2) :
    (differentialSolutions hq.ne_zero (K - 1) Q).card ≤ q ^ (2 * d + 4) := by
  have hKq : K ≤ q := hKn.le.trans hnq
  exact (differentialSolutions_card_le_sharp
    hq hdK hB Q hQ hcoord hBq hKq hweight).trans
      (sharpRootCount_le_publicBound hdK hKn hnq hBq)

/-- With weighted degree below `q`, both the extension and its extra exponent
disappear; the polynomial prefactors absorb into `q²`. -/
theorem differentialSolutions_card_le_baseField_public {q d K n B : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hKn : K < n) (hnq : n ≤ q)
    (hB : 0 < B)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q) :
    (differentialSolutions hq.ne_zero (K - 1) Q).card ≤ q ^ (d + 3) := by
  have hKq : K ≤ q := hKn.le.trans hnq
  exact (differentialSolutions_card_le_baseField
    hq hdK hB Q hQ hcoord hBq hKq hweight).trans
      (baseFieldRootCount_le_publicBound hdK hKn hnq hBq)

end RSListDecoding
