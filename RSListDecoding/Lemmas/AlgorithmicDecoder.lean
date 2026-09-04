import RSListDecoding.Lemmas.AlgorithmicInterpolation
import RSListDecoding.Lemmas.AlgorithmicRootCount
import RSListDecoding.Lemmas.InterpolationVanishing

/-!
# The costed Reed--Solomon list decoder

This module composes the checked interpolation solver, Kopparty's external
root enumerator, and an explicit final subcode/agreement filter.  Its main
correctness theorem identifies the returned finite set exactly with
`decodingList`; soundness and completeness are therefore both covered.
-/

noncomputable section

namespace RSListDecoding

/-- Charged work for checking one ambient root candidate.  The first `K`
tests check that high coefficients vanish.  At each of `n` points the direct
degree-`<K` evaluation is allocated `K²+2K` arithmetic operations and one
equality test.  This is a deliberately loose bound for the straightforward
finite-sum implementation. -/
def candidateFilterOperations (n K : ℕ) : ℕ :=
  K + n * (K ^ 2 + 2 * K + 1)

/-- Restrict the enumerated ambient roots to the requested subcode and exact
agreement threshold. -/
def filterAmbientRoots {n q k K : ℕ} (hkK : k ≤ K)
    (alpha : Fin n → ZMod q) (y : Fin n → ZMod q) (A : ℕ)
    (roots : Finset (Message q K)) : FieldCost (Finset (Message q k)) := by
  classical
  exact FieldCost.charge (roots.card * candidateFilterOperations n K)
    ((roots.filter fun p ↦
      ComesFromSubcode hkK p ∧ A ≤ agreementCount alpha y p).image
        (restrictMessage hkK))

@[simp]
theorem filterAmbientRoots_operations {n q k K : ℕ}
    (hkK : k ≤ K) (alpha : Fin n → ZMod q) (y : Fin n → ZMod q)
    (A : ℕ) (roots : Finset (Message q K)) :
    (filterAmbientRoots hkK alpha y A roots).operations =
      roots.card * candidateFilterOperations n K := rfl

/-- If `roots` contains the ambient decoding list, the final filter returns
exactly the requested smaller decoding list.  Extra differential-equation
roots are harmless. -/
theorem filterAmbientRoots_result_eq_decodingList
    {n q k K A : ℕ} (hq : q ≠ 0) (hkK : k ≤ K)
    (alpha : Fin n → ZMod q) (y : Fin n → ZMod q)
    (roots : Finset (Message q K))
    (hcontains : decodingList (k := K) hq alpha y A ⊆ roots) :
    (filterAmbientRoots hkK alpha y A roots).result =
      decodingList (k := k) hq alpha y A := by
  classical
  letI : NeZero q := ⟨hq⟩
  ext p
  constructor
  · intro hp
    change p ∈ ((roots.filter fun ambient ↦
      ComesFromSubcode hkK ambient ∧
        A ≤ agreementCount alpha y ambient).image
          (restrictMessage hkK)) at hp
    obtain ⟨ambient, hambient, hp⟩ := Finset.mem_image.mp hp
    obtain ⟨_hroot, hsubcode, hagree⟩ := Finset.mem_filter.mp hambient
    subst p
    rw [mem_decodingList]
    rw [← agreementCount_extendMessage hkK]
    rw [hsubcode]
    exact hagree
  · intro hp
    have hpAgreement := (mem_decodingList hq alpha y A p).mp hp
    let ambient := extendMessage hkK p
    have hambientList : ambient ∈ decodingList (k := K) hq alpha y A :=
      (extendMessage_mem_decodingList_iff hq hkK alpha y A p).mpr hp
    have hambientRoot : ambient ∈ roots := hcontains hambientList
    change p ∈ ((roots.filter fun ambient ↦
      ComesFromSubcode hkK ambient ∧
        A ≤ agreementCount alpha y ambient).image
          (restrictMessage hkK))
    apply Finset.mem_image.mpr
    refine ⟨ambient, Finset.mem_filter.mpr ⟨hambientRoot,
      comesFromSubcode_extendMessage hkK p, ?_⟩, ?_⟩
    · simpa [ambient, agreementCount_extendMessage] using hpAgreement
    · exact restrictMessage_extendMessage hkK p

/-- The complete decoder at fixed interpolation parameters.  Its result is
constructed by the three phases appearing in the paper: interpolation, root
enumeration, and filtering. -/
def decoderProgram {n q d m A K B W C k : ℕ}
    (hq : Nat.Prime q) (hd : 0 < d) (hdK : d < K) (hB : 0 < B)
    (hkK : k ≤ K)
    (hmA : 0 < m * A) (hmAq : m * A ≤ q ^ 2)
    (hBq : B < q)
    (hdim :
      n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C))
    (alpha : Fin n → ZMod q) (y : Fin n → ZMod q) :
    FieldCost (Finset (Message q k)) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let interpolation := solveInterpolationConstraints hd hdim alpha y
  let Qsub := interpolation.result
  let Q : DifferentialPolynomial q d := Qsub.1
  have hQ : Q ≠ 0 := by
    intro hzero
    apply solveInterpolationConstraints_ne_zero hd hdim alpha y
    apply Subtype.ext
    exact hzero
  have hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B :=
    fun j ↦ degreeOf_jet_le_of_mem_interpolationSpace Qsub.2 j
  have hweightMA :
      Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < m * A :=
    weightedTotalDegree_lt_of_mem_interpolationSpace hmA Qsub.2
  have hweightQ :
      Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2 :=
    hweightMA.trans_le hmAq
  let roots := ambientDifferentialRootProgram
    hq hdK hB Q hQ hcoord hBq hweightQ
  let filtered := filterAmbientRoots hkK alpha y A roots.result
  exact ⟨filtered.result,
    interpolation.operations + roots.operations + filtered.operations⟩

/-- Decoder correctness: the returned set is exactly the desired decoding
list, not merely a sound sublist or a complete superset. -/
theorem decoderProgram_result_eq_decodingList
    {n q d m A K B W C k : ℕ}
    (hq : Nat.Prime q) (hd : 0 < d) (hdK : d < K) (hB : 0 < B)
    (hkK : k ≤ K)
    (hmA : 0 < m * A) (hmAq : m * A ≤ q ^ 2)
    (hBq : B < q)
    (hdim :
      n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C))
    (alpha : Fin n → ZMod q) (halpha : Function.Injective alpha)
    (y : Fin n → ZMod q) :
    (decoderProgram hq hd hdK hB hkK hmA hmAq hBq hdim alpha y).result =
      decodingList (k := k) hq.ne_zero alpha y A := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let interpolation := solveInterpolationConstraints hd hdim alpha y
  let Qsub := interpolation.result
  let Q : DifferentialPolynomial q d := Qsub.1
  have hQ : Q ≠ 0 := by
    intro hzero
    apply solveInterpolationConstraints_ne_zero hd hdim alpha y
    apply Subtype.ext
    exact hzero
  have hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B :=
    fun j ↦ degreeOf_jet_le_of_mem_interpolationSpace Qsub.2 j
  have hweightMA :
      Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < m * A :=
    weightedTotalDegree_lt_of_mem_interpolationSpace hmA Qsub.2
  have hweightQ :
      Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2 :=
    hweightMA.trans_le hmAq
  let roots := ambientDifferentialRootProgram
    hq hdK hB Q hQ hcoord hBq hweightQ
  have hconstraints : ∀ i : Fin n,
      SatisfiesLocalConstraints m (alpha i) (y i) Q :=
    solveInterpolationConstraints_satisfies hd hdim alpha y
  have hcontains : decodingList (k := K) hq.ne_zero alpha y A ⊆ roots.result := by
    intro p hp
    rw [mem_ambientDifferentialRootProgram_result_iff]
    exact decodingList_candidate_solves_of_constraints
      hq (Nat.zero_lt_of_lt hdK) hmA alpha halpha y Qsub.2
        hconstraints p hp
  change (filterAmbientRoots hkK alpha y A roots.result).result = _
  exact filterAmbientRoots_result_eq_decodingList
    hq.ne_zero hkK alpha y roots.result hcontains

/-- Exact additive cost bound for the three decoder phases. -/
theorem decoderProgram_operations_le
    {n q d m A K B W C k : ℕ}
    (hq : Nat.Prime q) (hd : 0 < d) (hdK : d < K)
    (hKn : K < n) (hnq : n ≤ q) (hB : 0 < B) (hkK : k ≤ K)
    (hmA : 0 < m * A) (hmAq : m * A ≤ q ^ 2)
    (hBq : B < q)
    (hdim :
      n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C))
    (alpha : Fin n → ZMod q) (y : Fin n → ZMod q) :
    (decoderProgram hq hd hdK hB hkK hmA hmAq hBq hdim alpha y).operations ≤
      (interpolationMatrixOperationsFull n d m A K B W C +
        (8 * (n * Nat.card (ContactEnvelopeCoordinate d m W)) *
            Nat.card (InterpolationColumn d m A K B W C) ^ 2 +
          Nat.card (InterpolationColumn d m A K B W C))) +
      q ^ (kopparty_theorem_4_3_algorithm.exponentConstant * (d + 1)) +
      q ^ (4 * d + 6) * candidateFilterOperations n K := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let interpolation := solveInterpolationConstraints hd hdim alpha y
  let Qsub := interpolation.result
  let Q : DifferentialPolynomial q d := Qsub.1
  have hQ : Q ≠ 0 := by
    intro hzero
    apply solveInterpolationConstraints_ne_zero hd hdim alpha y
    apply Subtype.ext
    exact hzero
  have hcoord : ∀ j : Fin (d + 1), Q.degreeOf (some j) ≤ B :=
    fun j ↦ degreeOf_jet_le_of_mem_interpolationSpace Qsub.2 j
  have hweightMA :
      Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < m * A :=
    weightedTotalDegree_lt_of_mem_interpolationSpace hmA Qsub.2
  have hweightQ :
      Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < q ^ 2 :=
    hweightMA.trans_le hmAq
  let roots := ambientDifferentialRootProgram
    hq hdK hB Q hQ hcoord hBq hweightQ
  have hinterpolation :=
    solveInterpolationConstraints_operations_le hd hdim alpha y
  have hroot := ambientDifferentialRootProgram_operations_le
    hq hdK hB Q hQ hcoord hBq (hKn.le.trans hnq) hweightQ
  have hrootcard := ambientDifferentialRootProgram_card_le_public
    hq hdK hKn hnq hB Q hQ hcoord hBq hweightQ
  change interpolation.operations + roots.operations +
      roots.result.card * candidateFilterOperations n K ≤ _
  exact Nat.add_le_add
    (Nat.add_le_add hinterpolation hroot)
    (Nat.mul_le_mul_right _ hrootcard)

end RSListDecoding
