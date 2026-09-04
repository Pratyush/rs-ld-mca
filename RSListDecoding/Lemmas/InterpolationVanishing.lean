import RSListDecoding.Lemmas.Contact
import RSListDecoding.Lemmas.GlobalBudgets
import RSListDecoding.Lemmas.MultiplicityRoots
import RSListDecoding.Lemmas.SolutionListBridge
import RSListDecoding.Lemmas.Subcode
import Mathlib.Algebra.Field.ZMod

/-!
# Vanishing of the interpolant on every decoding-list candidate

At an agreement coordinate, the local interpolation conditions give a root
of multiplicity `m` of the differential specialization.  Injectivity of the
evaluation points makes these roots distinct.  The global weighted-degree
budget then forces the specialization to vanish identically for every
message with at least `A` agreements.
-/

noncomputable section

namespace RSListDecoding

open Polynomial

/-- The polynomial associated to a coefficient vector of length `D + 1` has
natural degree at most `D`. -/
theorem messagePolynomial_natDegree_le {q D : ℕ}
    (p : Message q (D + 1)) :
    (messagePolynomial p).natDegree ≤ D := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hDN
  have hdegree := messagePolynomial_degree_lt p
  rw [Polynomial.degree_lt_iff_coeff_zero] at hdegree
  exact hdegree N (by omega)

/-- The positive-dimension transport used by the root-counting interface
retains the expected degree cap. -/
theorem messagePolynomialAtDimension_natDegree_le {q K : ℕ}
    (hK : 0 < K) (p : Message q K) :
    (messagePolynomialAtDimension hK p).natDegree ≤ K - 1 := by
  exact messagePolynomial_natDegree_le (messageDegreeCapEquiv hK p)

/-- Every ambient decoding-list candidate annihilates an interpolant that
satisfies all received-word constraints and the global support budget. -/
theorem decodingList_candidate_solves_of_constraints
    {n q d m A K B W C : ℕ}
    (hq : Nat.Prime q) (hK : 0 < K) (hmA : 0 < m * A)
    (alpha : Fin n → ZMod q) (halpha : Function.Injective alpha)
    (y : Fin n → ZMod q) {Q : DifferentialPolynomial q d}
    (hQspace : Q ∈ interpolationSpace q d m A K B W C)
    (hconstraints : ∀ i : Fin n,
      SatisfiesLocalConstraints m (alpha i) (y i) Q)
    (p : Message q K)
    (hp : p ∈ decodingList hq.ne_zero alpha y A) :
    differentialSpecialization Q
        (messagePolynomialAtDimension hK p) = 0 := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let S : Finset (Fin n) :=
    Finset.univ.filter fun i => evaluateMessage p (alpha i) = y i
  apply eq_zero_of_natDegree_lt_agreement_mul_of_pow_X_sub_C_dvd
    alpha halpha S
  · have hp' := (mem_decodingList hq.ne_zero alpha y A p).mp hp
    simpa [agreementCount, S] using hp'
  · intro i hi
    have hagree : evaluateMessage p (alpha i) = y i :=
      (Finset.mem_filter.mp hi).2
    apply pow_X_sub_C_dvd_differentialSpecialization_of_contact
      Q (messagePolynomialAtDimension hK p) (alpha i) (y i)
    · simpa using hagree
    · exact hconstraints i
  · exact natDegree_differentialSpecialization_lt_of_mem_interpolationSpace
      hmA hQspace (messagePolynomialAtDimension hK p)
        (messagePolynomialAtDimension_natDegree_le hK p)

/-- Package a nonzero constrained interpolation polynomial into exactly the
explainer tuple consumed by the list-size reduction. -/
theorem ambient_explainer_of_nonzero_interpolant
    {n q d m A K B W C : ℕ}
    (hq : Nat.Prime q) (hK : 0 < K) (hmA : 0 < m * A)
    (alpha : Fin n → ZMod q) (halpha : Function.Injective alpha)
    (y : Fin n → ZMod q) {Q : DifferentialPolynomial q d}
    (hQne : Q ≠ 0)
    (hQspace : Q ∈ interpolationSpace q d m A K B W C)
    (hconstraints : ∀ i : Fin n,
      SatisfiesLocalConstraints m (alpha i) (y i) Q) :
    Q ≠ 0 ∧
      (∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B) ∧
      Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < m * A ∧
      ∀ p ∈ decodingList (k := K) hq.ne_zero alpha y A,
        differentialSpecialization Q
          (messagePolynomialAtDimension hK p) = 0 := by
  refine ⟨hQne, fun j => degreeOf_jet_le_of_mem_interpolationSpace hQspace j,
    weightedTotalDegree_lt_of_mem_interpolationSpace hmA hQspace, ?_⟩
  intro p hp
  exact decodingList_candidate_solves_of_constraints
    hq hK hmA alpha halpha y hQspace hconstraints p hp

/-- Existential form convenient after applying the interpolation-kernel
theorem. -/
theorem exists_ambient_explainer_of_nonzero_interpolant
    {n q d m A K B W C : ℕ}
    (hq : Nat.Prime q) (hK : 0 < K) (hmA : 0 < m * A)
    (alpha : Fin n → ZMod q) (halpha : Function.Injective alpha)
    (y : Fin n → ZMod q)
    (hexists : ∃ Q : DifferentialPolynomial q d,
      Q ≠ 0 ∧ Q ∈ interpolationSpace q d m A K B W C ∧
        ∀ i : Fin n, SatisfiesLocalConstraints m (alpha i) (y i) Q) :
    ∃ Q : DifferentialPolynomial q d,
      Q ≠ 0 ∧
      (∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B) ∧
      Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < m * A ∧
      ∀ p ∈ decodingList (k := K) hq.ne_zero alpha y A,
        differentialSpecialization Q
          (messagePolynomialAtDimension hK p) = 0 := by
  obtain ⟨Q, hQne, hQspace, hconstraints⟩ := hexists
  exact ⟨Q, ambient_explainer_of_nonzero_interpolant
    hq hK hmA alpha halpha y hQne hQspace hconstraints⟩

end RSListDecoding
