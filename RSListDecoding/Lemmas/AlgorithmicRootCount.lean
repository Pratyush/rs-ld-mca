import RSListDecoding.Assumptions
import RSListDecoding.Lemmas.SolutionListBridge

/-!
# Algorithmic specialization of Kopparty's root theorem

The opaque root solver is the sole external algorithmic input.  This file
performs only checked specialization and the harmless coefficient-vector cast
from length `(K-1)+1` to length `K`.
-/

noncomputable section

namespace RSListDecoding

/-- Package the ambient interpolation polynomial as a valid input to
Kopparty's root algorithm. -/
def ambientKoppartyRootInput {q d K B : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hB : 0 < B)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2) :
    KoppartyRootInput where
  q := q
  r := d
  D := K - 1
  t := B
  prime := hq
  order_le_degree := by omega
  parameter_pos := hB
  polynomial := Q
  polynomial_ne_zero := hQ
  coordinate_degree := hcoord
  parameter_lt_field := hBq
  weighted_degree := hweight

/-- Costed enumeration of all ambient degree-`<K` solutions. -/
def ambientDifferentialRootProgram {q d K B : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hB : 0 < B)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2) :
    FieldCost (Finset (Message q K)) :=
  let input := ambientKoppartyRootInput hq hdK hB Q hQ hcoord hBq hweight
  let raw := kopparty_theorem_4_3_algorithm.solve input
  FieldCost.map
    (fun solutions ↦ solutions.map
      (messageDegreeCapEquiv (Nat.zero_lt_of_lt hdK)).symm.toEmbedding)
    raw

/-- The external root program returns exactly the degree-`<K` solutions of
the supplied differential equation. -/
theorem mem_ambientDifferentialRootProgram_result_iff
    {q d K B : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hB : 0 < B)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2)
    (p : Message q K) :
    p ∈ (ambientDifferentialRootProgram hq hdK hB Q hQ hcoord hBq hweight).result ↔
      differentialSpecialization Q
        (messagePolynomialAtDimension (Nat.zero_lt_of_lt hdK) p) = 0 := by
  let input := ambientKoppartyRootInput hq hdK hB Q hQ hcoord hBq hweight
  let e := messageDegreeCapEquiv (q := q) (Nat.zero_lt_of_lt hdK)
  rw [ambientDifferentialRootProgram]
  change p ∈ (kopparty_theorem_4_3_algorithm.solve input).result.map
    e.symm.toEmbedding ↔ _
  rw [kopparty_theorem_4_3_algorithm.exact_output]
  rw [Finset.mem_map]
  constructor
  · rintro ⟨raw, hraw, hp⟩
    change e.symm raw = p at hp
    have hraw_eq : raw = e p := by
      apply e.symm.injective
      simpa using hp
    subst raw
    change e p ∈ differentialSolutions hq.ne_zero (K - 1) Q at hraw
    change differentialSpecialization Q (messagePolynomial (e p)) = 0
    exact (mem_differentialSolutions hq.ne_zero Q (e p)).mp hraw
  · intro hp
    refine ⟨e p, ?_, by simp⟩
    change e p ∈ differentialSolutions hq.ne_zero (K - 1) Q
    change differentialSpecialization Q (messagePolynomial (e p)) = 0 at hp
    exact (mem_differentialSolutions hq.ne_zero Q (e p)).mpr hp

/-- When `K ≤ q`, the source exponent collapses from
`d + d floor((K-1)/q) + 1` to `d+1`. -/
theorem ambientDifferentialRootProgram_operations_le
    {q d K B : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hB : 0 < B)
    (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q) (hKq : K ≤ q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2) :
    (ambientDifferentialRootProgram hq hdK hB Q hQ hcoord hBq hweight).operations ≤
      q ^ (kopparty_theorem_4_3_algorithm.exponentConstant * (d + 1)) := by
  let input := ambientKoppartyRootInput hq hdK hB Q hQ hcoord hBq hweight
  have hsource := kopparty_theorem_4_3_algorithm.operations_le input
  have hDq : K - 1 < q := by omega
  simpa [ambientDifferentialRootProgram, input,
    ambientKoppartyRootInput, Nat.div_eq_of_lt hDq, Nat.add_assoc] using hsource

/-- The enumerated root set obeys the already checked public cardinality
bound. -/
theorem ambientDifferentialRootProgram_card_le_public
    {q d K n B : ℕ}
    (hq : Nat.Prime q) (hdK : d < K) (hKn : K < n) (hnq : n ≤ q)
    (hB : 0 < B) (Q : DifferentialPolynomial q d) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B)
    (hBq : B < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2) :
    (ambientDifferentialRootProgram hq hdK hB Q hQ hcoord hBq hweight).result.card ≤
      q ^ (2 * d + 4) := by
  let input := ambientKoppartyRootInput hq hdK hB Q hQ hcoord hBq hweight
  let e := messageDegreeCapEquiv (q := q) (Nat.zero_lt_of_lt hdK)
  change ((kopparty_theorem_4_3_algorithm.solve input).result.map
    e.symm.toEmbedding).card ≤ _
  rw [Finset.card_map, kopparty_theorem_4_3_algorithm.exact_output]
  change (differentialSolutions hq.ne_zero (K - 1) Q).card ≤ _
  exact differentialSolutions_card_le_public
    hq hdK hKn hnq hB Q hQ hcoord hBq hweight

end RSListDecoding
