import RSListDecoding.Lemmas.RootCount

/-!
# From decoding lists to differential-equation solution sets

This module connects the coefficient-vector representation of Reed--Solomon
messages to the polynomial representation used by the differential-equation
root count.  It then packages the finite-set inclusion which turns a common
differential equation for every word in a decoding list into a cardinality
bound for that list.
-/

noncomputable section

namespace RSListDecoding

/-- `messagePolynomial` has exactly the coefficients of its input vector. -/
@[simp]
theorem messagePolynomial_coeff {q D : ℕ} (p : Message q (D + 1))
    (i : Fin (D + 1)) :
    (messagePolynomial p).coeff (i : ℕ) = p i := by
  change (Polynomial.degreeLTEquiv (ZMod q) (D + 1)
    ((Polynomial.degreeLTEquiv (ZMod q) (D + 1)).symm p)) i = p i
  simp

/-- Evaluating the polynomial associated to a coefficient vector agrees
exactly with the direct finite-sum definition of message evaluation. -/
@[simp]
theorem messagePolynomial_eval {q D : ℕ} (p : Message q (D + 1))
    (x : ZMod q) :
    (messagePolynomial p).eval x = evaluateMessage p x := by
  let P := (Polynomial.degreeLTEquiv (ZMod q) (D + 1)).symm p
  have h := Polynomial.eval_eq_sum_degreeLTEquiv P.property x
  simpa [messagePolynomial, evaluateMessage, P] using h

/-- A positive-dimensional coefficient space is canonically the
degree-at-most-`K-1` coefficient space expected by the root-counting theorem.
The explicit equivalence keeps the identity `(K-1)+1=K` out of downstream
dependent casts. -/
def messageDegreeCapEquiv {q K : ℕ} (hK : 0 < K) :
    Message q K ≃ Message q (K - 1 + 1) :=
  Equiv.cast <| congrArg (Message q) <|
    (Nat.sub_add_cancel (Nat.succ_le_iff.mpr hK)).symm

/-- Regard a positive-dimensional message as the degree-at-most-`K-1`
polynomial used by the differential-equation root count. -/
def messagePolynomialAtDimension {q K : ℕ} (hK : 0 < K)
    (p : Message q K) : Polynomial (ZMod q) :=
  messagePolynomial (messageDegreeCapEquiv hK p)

/-- The positive-dimension transport does not change message evaluation. -/
@[simp]
theorem messagePolynomialAtDimension_eval {q K : ℕ} (hK : 0 < K)
    (p : Message q K) (x : ZMod q) :
    (messagePolynomialAtDimension hK p).eval x = evaluateMessage p x := by
  cases K with
  | zero => omega
  | succ K =>
      simp [messagePolynomialAtDimension, messageDegreeCapEquiv]
      rfl

/-- If every word in a decoding list solves one fixed differential equation,
then the list is no larger than the full finite set of degree-bounded
solutions of that equation. -/
theorem decodingList_card_le_differentialSolutions {n q r D A : ℕ}
    (hq : q ≠ 0) (alpha : Fin n → ZMod q) (y : Fin n → ZMod q)
    (Q : DifferentialPolynomial q r)
    (hsolves : ∀ p ∈ decodingList (k := D + 1) hq alpha y A,
      differentialSpecialization Q (messagePolynomial p) = 0) :
    (decodingList (k := D + 1) hq alpha y A).card ≤
      (differentialSolutions hq D Q).card := by
  apply Finset.card_le_card
  intro p hp
  exact (mem_differentialSolutions hq Q p).2 (hsolves p hp)

/-- Positive-dimension form of `decodingList_card_le_differentialSolutions`.
The canonical equivalence transports dimension `K` to the root theorem's
coefficient-vector length `(K-1)+1`. -/
theorem decodingList_card_le_differentialSolutions_at_dimension
    {n q r K A : ℕ} (hq : q ≠ 0) (hK : 0 < K)
    (alpha : Fin n → ZMod q) (y : Fin n → ZMod q)
    (Q : DifferentialPolynomial q r)
    (hsolves : ∀ p ∈ decodingList (k := K) hq alpha y A,
      differentialSpecialization Q (messagePolynomialAtDimension hK p) = 0) :
    (decodingList (k := K) hq alpha y A).card ≤
      (differentialSolutions hq (K - 1) Q).card := by
  let e : Message q K ≃ Message q (K - 1 + 1) := messageDegreeCapEquiv hK
  have hsubset : (decodingList (k := K) hq alpha y A).map e.toEmbedding ⊆
      differentialSolutions hq (K - 1) Q := by
    intro p hp
    rw [Finset.mem_map] at hp
    obtain ⟨p, hp, rfl⟩ := hp
    exact (mem_differentialSolutions hq Q (e p)).2 (hsolves p hp)
  calc
    (decodingList (k := K) hq alpha y A).card =
        ((decodingList (k := K) hq alpha y A).map e.toEmbedding).card :=
      (Finset.card_map e.toEmbedding).symm
    _ ≤ (differentialSolutions hq (K - 1) Q).card :=
      Finset.card_le_card hsubset

/-- A common differential equation satisfying the public root-count
hypotheses gives the public decoding-list bound. -/
theorem decodingList_card_le_public_of_differentialEquation
    {n q d K B A : ℕ} (hq : Nat.Prime q) (hdK : d < K)
    (hKn : K < n) (hnq : n ≤ q) (hB : 0 < B)
    (alpha : Fin n → ZMod q) (y : Fin n → ZMod q)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2)
    (hsolves : ∀ p ∈ decodingList (k := K) hq.ne_zero alpha y A,
      differentialSpecialization Q
        (messagePolynomialAtDimension (Nat.zero_lt_of_lt hdK) p) = 0) :
    (decodingList (k := K) hq.ne_zero alpha y A).card ≤ q ^ (2 * d + 4) := by
  have hK : 0 < K := Nat.zero_lt_of_lt hdK
  exact (decodingList_card_le_differentialSolutions_at_dimension
    hq.ne_zero hK alpha y Q hsolves).trans
      (differentialSolutions_card_le_public
        hq hdK hKn hnq hB Q hQ hcoord hBq hweight)

/-- A common differential equation gives the exact Kopparty cardinality
bound, without absorbing `B(d+1)` into two additional powers of `q`. -/
theorem decodingList_card_le_sharp_of_differentialEquation
    {n q d K B A : ℕ} (hq : Nat.Prime q) (hdK : d < K)
    (hB : 0 < B) (hKq : K ≤ q)
    (alpha : Fin n → ZMod q) (y : Fin n → ZMod q)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2)
    (hsolves : ∀ p ∈ decodingList (k := K) hq.ne_zero alpha y A,
      differentialSpecialization Q
        (messagePolynomialAtDimension (Nat.zero_lt_of_lt hdK) p) = 0) :
    (decodingList (k := K) hq.ne_zero alpha y A).card ≤
      B * rootCountGeometricFactor q 2 d := by
  have hK : 0 < K := Nat.zero_lt_of_lt hdK
  exact (decodingList_card_le_differentialSolutions_at_dimension
    hq.ne_zero hK alpha y Q hsolves).trans
      (differentialSolutions_card_le_sharp
        hq hdK hB Q hQ hcoord hBq hKq hweight)

/-- Exact base-field root bound.  This version applies when the weighted
degree is below `q`, rather than merely below `q²`. -/
theorem decodingList_card_le_baseField_of_differentialEquation
    {n q d K B A : ℕ} (hq : Nat.Prime q) (hdK : d < K)
    (hB : 0 < B) (hKq : K ≤ q)
    (alpha : Fin n → ZMod q) (y : Fin n → ZMod q)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q)
    (hsolves : ∀ p ∈ decodingList (k := K) hq.ne_zero alpha y A,
      differentialSpecialization Q
        (messagePolynomialAtDimension (Nat.zero_lt_of_lt hdK) p) = 0) :
    (decodingList (k := K) hq.ne_zero alpha y A).card ≤
      B * rootCountGeometricFactor q 1 d := by
  have hK : 0 < K := Nat.zero_lt_of_lt hdK
  exact (decodingList_card_le_differentialSolutions_at_dimension
    hq.ne_zero hK alpha y Q hsolves).trans
      (differentialSolutions_card_le_baseField
        hq hdK hB Q hQ hcoord hBq hKq hweight)

end RSListDecoding
