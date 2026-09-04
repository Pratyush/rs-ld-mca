import RSListDecoding.Lemmas.SolutionListBridge
import RSListDecoding.Lemmas.Subcode

/-!
# From explainer existence to list decodability

This file isolates the final finite-set argument from the interpolation
construction.  Its input is exactly what interpolation must produce for each
received word: one nonzero differential polynomial of controlled coordinate
degrees and weighted degree that vanishes on every candidate message.
-/

noncomputable section

namespace RSListDecoding

/-- If every received word admits a controlled explainer at ambient dimension
`K`, then the ambient Reed--Solomon code has the public list bound. -/
theorem isListDecodableAtAgreement_of_ambient_explainers
    {n q d K B A M : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hKn : K < n) (hnq : n ≤ q)
    (hB : 0 < B) (hBq : B < q) (hMq : M ≤ q ^ 2)
    (alpha : Fin n → ZMod q)
    (hexplainer : ∀ y : Fin n → ZMod q,
      ∃ Q : DifferentialPolynomial q d,
        Q ≠ 0 ∧
        (∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B) ∧
        Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < M ∧
        ∀ p ∈ decodingList (k := K) hq.ne_zero alpha y A,
          differentialSpecialization Q
            (messagePolynomialAtDimension (Nat.zero_lt_of_lt hdK) p) = 0) :
    IsListDecodableAtAgreement (k := K) hq.ne_zero alpha A
      (q ^ (2 * d + 4)) := by
  intro y
  obtain ⟨Q, hQ, hcoord, hweight, hsolves⟩ := hexplainer y
  exact decodingList_card_le_public_of_differentialEquation
    hq hdK hKn hnq hB alpha y Q hQ hcoord hBq
      (hweight.trans_le hMq) hsolves

/-- The same explainer at the ambient dimension controls every smaller
degree-`< k` Reed--Solomon subcode. -/
theorem isListDecodableAtAgreement_of_ambient_explainers_of_le_dimension
    {n q d k K B A M : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hkK : k ≤ K)
    (hKn : K < n) (hnq : n ≤ q)
    (hB : 0 < B) (hBq : B < q) (hMq : M ≤ q ^ 2)
    (alpha : Fin n → ZMod q)
    (hexplainer : ∀ y : Fin n → ZMod q,
      ∃ Q : DifferentialPolynomial q d,
        Q ≠ 0 ∧
        (∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B) ∧
        Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < M ∧
        ∀ p ∈ decodingList (k := K) hq.ne_zero alpha y A,
          differentialSpecialization Q
            (messagePolynomialAtDimension (Nat.zero_lt_of_lt hdK) p) = 0) :
    IsListDecodableAtAgreement (k := k) hq.ne_zero alpha A
      (q ^ (2 * d + 4)) := by
  apply isListDecodableAtAgreement_of_le_dimension hq.ne_zero hkK alpha
  exact isListDecodableAtAgreement_of_ambient_explainers
    hq hdK hKn hnq hB hBq hMq alpha hexplainer

/-- Exact-prefactor version of the ambient-explainer reduction. -/
theorem isListDecodableAtAgreement_sharp_of_ambient_explainers_of_le_dimension
    {n q d k K B A M : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hkK : k ≤ K)
    (hKq : K ≤ q) (hB : 0 < B) (hBq : B < q) (hMq : M ≤ q ^ 2)
    (alpha : Fin n → ZMod q)
    (hexplainer : ∀ y : Fin n → ZMod q,
      ∃ Q : DifferentialPolynomial q d,
        Q ≠ 0 ∧
        (∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B) ∧
        Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < M ∧
        ∀ p ∈ decodingList (k := K) hq.ne_zero alpha y A,
          differentialSpecialization Q
            (messagePolynomialAtDimension (Nat.zero_lt_of_lt hdK) p) = 0) :
    IsListDecodableAtAgreement (k := k) hq.ne_zero alpha A
      (B * rootCountGeometricFactor q 2 d) := by
  apply isListDecodableAtAgreement_of_le_dimension hq.ne_zero hkK alpha
  intro y
  obtain ⟨Q, hQ, hcoord, hweight, hsolves⟩ := hexplainer y
  exact decodingList_card_le_sharp_of_differentialEquation
    hq hdK hB hKq alpha y Q hQ hcoord hBq
      (hweight.trans_le hMq) hsolves

/-- Base-field version of the ambient-explainer reduction.  The stronger
weighted-degree hypothesis eliminates the quadratic extension in the root
count and halves the remaining field exponent. -/
theorem isListDecodableAtAgreement_baseField_of_ambient_explainers_of_le_dimension
    {n q d k K B A M : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hkK : k ≤ K)
    (hKq : K ≤ q) (hB : 0 < B) (hBq : B < q) (hMq : M ≤ q)
    (alpha : Fin n → ZMod q)
    (hexplainer : ∀ y : Fin n → ZMod q,
      ∃ Q : DifferentialPolynomial q d,
        Q ≠ 0 ∧
        (∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B) ∧
        Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < M ∧
        ∀ p ∈ decodingList (k := K) hq.ne_zero alpha y A,
          differentialSpecialization Q
            (messagePolynomialAtDimension (Nat.zero_lt_of_lt hdK) p) = 0) :
    IsListDecodableAtAgreement (k := k) hq.ne_zero alpha A
      (B * rootCountGeometricFactor q 1 d) := by
  apply isListDecodableAtAgreement_of_le_dimension hq.ne_zero hkK alpha
  intro y
  obtain ⟨Q, hQ, hcoord, hweight, hsolves⟩ := hexplainer y
  exact decodingList_card_le_baseField_of_differentialEquation
    hq hdK hB hKq alpha y Q hQ hcoord hBq
      (hweight.trans_le hMq) hsolves

/-- Parameterized form of the preceding reduction matching the public
capstone.  After this theorem, the only mathematical input still needed at a
fixed `(θ, ε, n)` is the construction of the explainer polynomial. -/
theorem scoped_list_bound_of_ambient_explainers
    {ε θ : ℝ} {n k q : ℕ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hn : 0 < n)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n)
    (hkK : k ≤ ambientDimension ε θ n)
    (hq : Nat.Prime q) (hnq : n ≤ q)
    (hBq : interpolationDegreeBudget ε θ n < q)
    (hMq : multiplicity ε θ * agreementThreshold ε n ≤ q ^ 2)
    (alpha : Fin n → ZMod q)
    (hexplainer : ∀ y : Fin n → ZMod q,
      ∃ Q : DifferentialPolynomial q (derivativeOrder ε θ),
        Q ≠ 0 ∧
        (∀ j : Fin (derivativeOrder ε θ + 1),
          Q.degreeOf (some j) ≤ interpolationDegreeBudget ε θ n) ∧
        Q.weightedTotalDegree
            (jetWeight (r := derivativeOrder ε θ)
              (ambientDimension ε θ n - 1)) <
          multiplicity ε θ * agreementThreshold ε n ∧
        ∀ p ∈ decodingList (k := ambientDimension ε θ n) hq.ne_zero
            alpha y (agreementThreshold ε n),
          differentialSpecialization Q
            (messagePolynomialAtDimension
              (Nat.zero_lt_of_lt hdK) p) = 0) :
    IsListDecodableAtAgreement (k := k) hq.ne_zero alpha
      (agreementThreshold ε n) (publicListBound q ε θ) := by
  have hKn : ambientDimension ε θ n < n :=
    ambientDimension_lt_blockLength hε hε₁ hθ hθ₁ hn
  have hB : 0 < interpolationDegreeBudget ε θ n :=
    interpolationDegreeBudget_pos hε hn hdK
  simpa only [publicListBound] using
    isListDecodableAtAgreement_of_ambient_explainers_of_le_dimension
      hq hdK hkK hKn hnq hB hBq hMq alpha hexplainer

end RSListDecoding
