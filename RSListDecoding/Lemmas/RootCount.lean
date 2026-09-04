import RSListDecoding.Assumptions
import RSListDecoding.Lemmas.Parameters

/-!
# Cardinality bounds for polynomial differential equations

This module contains checked arithmetic specializations of the sole external
root-counting input.  In the application the solution degree is `K-1 < q`, so
the quotient `⌊(K-1)/q⌋` vanishes and Kopparty's bound has exponent `4d+4`.
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

/-- Kopparty's cardinality bound when the solution degree is smaller than the
field size.  The source hypothesis is the inclusive individual-degree bound
`degreeOf (some j) Q ≤ t`; no strict-degree reinterpretation occurs here. -/
theorem kopparty_cardinality_of_degree_lt_field {q r D t : ℕ}
    (hq : Nat.Prime q) (hrD : r ≤ D) (ht : 0 < t)
    (Q : DifferentialPolynomial q r) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (r + 1), Q.degreeOf (some j) ≤ t)
    (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < q ^ 2)
    (hDq : D < q) :
    (differentialSolutions hq.ne_zero D Q).card ≤
      t * (r + 1) * q ^ (4 * r + 4) := by
  simpa [Nat.div_eq_of_lt hDq] using
    kopparty_theorem_4_3_cardinality hq hrD ht Q hQ hcoord htq hweight

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
      B * (d + 1) * q ^ (4 * d + 4) := by
  have hdD : d ≤ K - 1 := by omega
  have hDq : K - 1 < q := by omega
  exact kopparty_cardinality_of_degree_lt_field
    hq hdD hB Q hQ hcoord hBq hweight hDq

/-- The sharp differential-equation count fits into the public
`q^(4d+6)` list bound under the scope's ambient-dimension and field-size
hypotheses. -/
theorem differentialSolutions_card_le_public {q d K n B : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hKn : K < n) (hnq : n ≤ q)
    (hB : 0 < B)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2) :
    (differentialSolutions hq.ne_zero (K - 1) Q).card ≤ q ^ (4 * d + 6) := by
  have hKq : K ≤ q := hKn.le.trans hnq
  exact (differentialSolutions_card_le_sharp
    hq hdK hB Q hQ hcoord hBq hKq hweight).trans
      (sharpRootCount_le_publicBound hdK hKn hnq hBq)

end RSListDecoding
