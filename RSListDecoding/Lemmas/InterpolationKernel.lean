import RSListDecoding.Lemmas.ConstraintFactorization
import RSListDecoding.Lemmas.ConstraintMap
import RSListDecoding.Lemmas.ContactEnvelopeCount
import RSListDecoding.Lemmas.DimensionComparison
import RSListDecoding.Lemmas.LinearInterpolationKernel
import Mathlib.Algebra.Field.ZMod

/-!
# A nonzero interpolant satisfying every received-word constraint

The coordinate bookkeeping is now hidden behind one linear map per received
point.  Each map factors through the universal local space and takes values in
the finite contact envelope.  The generic common-kernel theorem then produces
a nonzero interpolation polynomial whenever the checked dimension inequality
holds.
-/

noncomputable section

namespace RSListDecoding

/-- The local constraint at one point, with its codomain restricted to the
finite contact envelope. -/
def pointConstraintMap {q d m A K B W C : ℕ}
    (alpha y : ZMod q) :
    interpolationSpace q d m A K B W C →ₗ[ZMod q]
      contactEnvelopeSpace (R := ZMod q) (d := d) m W :=
  LinearMap.codRestrict
    (contactEnvelopeSpace (R := ZMod q) (d := d) m W)
    ((receivedConstraintMap (R := ZMod q) (d := d) m alpha y).domRestrict
      (interpolationSpace q d m A K B W C))
    (fun Q => by
      change receivedConstraintMap (d := d) m alpha y Q.1 ∈
        contactEnvelopeSpace (R := ZMod q) (d := d) m W
      rw [receivedConstraintMap_eq_localConstraintMap_translatedTruncation]
      apply localConstraintMap_mem_contactEnvelopeSpace
      exact translatedTruncation_mem_localVSpace Q.2 alpha y)

@[simp]
theorem pointConstraintMap_coe {q d m A K B W C : ℕ}
    (alpha y : ZMod q) (Q : interpolationSpace q d m A K B W C) :
    (pointConstraintMap alpha y Q : LocalPolynomial (ZMod q) d) =
      receivedConstraintMap (d := d) m alpha y Q.1 :=
  rfl

/-- Vanishing in the finite codomain is exactly the manuscript's family of
local coefficient conditions. -/
theorem pointConstraintMap_eq_zero_iff_satisfiesLocalConstraints
    {q d m A K B W C : ℕ}
    (alpha y : ZMod q) (Q : interpolationSpace q d m A K B W C) :
    pointConstraintMap alpha y Q = 0 ↔
      SatisfiesLocalConstraints m alpha y Q.1 := by
  rw [satisfiesLocalConstraints_iff_receivedConstraintMap_eq_zero]
  constructor
  · intro h
    have := congrArg
      (fun F : contactEnvelopeSpace (R := ZMod q) (d := d) m W =>
        (F.1 : LocalPolynomial (ZMod q) d)) h
    simpa using this
  · intro h
    apply Subtype.ext
    simpa using h

/-- Dimension inequality form of interpolation existence. -/
theorem exists_nonzero_interpolant_satisfying_constraints
    {q d m A K B W C n : ℕ} [Fact (Nat.Prime q)]
    (hd : 0 < d)
    (hdim :
      n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C))
    (alpha y : Fin n → ZMod q) :
    ∃ Q : DifferentialPolynomial q d,
      Q ≠ 0 ∧ Q ∈ interpolationSpace q d m A K B W C ∧
      ∀ i : Fin n, SatisfiesLocalConstraints m (alpha i) (y i) Q := by
  let sourceBasis := interpolationSpaceBasis q d m A K B W C
  letI : Module.Finite (ZMod q)
      (interpolationSpace q d m A K B W C) :=
    Module.Finite.of_basis sourceBasis
  let code :
      {e : LocalVariable d →₀ ℕ // ContactEnvelopeExponent (d := d) m W e} →
        ContactEnvelopeCode d m W := encodeContactEnvelope hd
  letI : Fintype
      {e : LocalVariable d →₀ ℕ // ContactEnvelopeExponent (d := d) m W e} :=
    Fintype.ofInjective code (by
      simpa [code] using encodeContactEnvelope_injective (m := m) (W := W) hd)
  let targetBasis : Module.Basis
      {e : LocalVariable d →₀ ℕ // ContactEnvelopeExponent (d := d) m W e}
      (ZMod q) (contactEnvelopeSpace (R := ZMod q) (d := d) m W) :=
    MvPolynomial.basisRestrictSupport (ZMod q)
      {e | ContactEnvelopeExponent (d := d) m W e}
  letI : Module.Finite (ZMod q)
      (contactEnvelopeSpace (R := ZMod q) (d := d) m W) :=
    Module.Finite.of_basis targetBasis
  obtain ⟨Q, hQne, hQconstraints⟩ :=
    exists_ne_zero_forall_apply_eq_zero
      (F := ZMod q) (ι := Fin n)
      (fun i => pointConstraintMap (alpha i) (y i)) (by simpa using hdim)
  refine ⟨Q.1, ?_, Q.2, fun i => ?_⟩
  · intro hzero
    apply hQne
    apply Subtype.ext
    exact hzero
  · exact (pointConstraintMap_eq_zero_iff_satisfiesLocalConstraints
      (alpha i) (y i) Q).mp (hQconstraints i)

/-- The point constraint with the smaller coupled codomain. -/
def coupledPointConstraintMap {q d m A K B W C : ℕ}
    (alpha y : ZMod q) :
    interpolationSpace q d m A K B W C →ₗ[ZMod q]
      coupledContactEnvelopeSpace (R := ZMod q) (d := d) m W :=
  LinearMap.codRestrict
    (coupledContactEnvelopeSpace (R := ZMod q) (d := d) m W)
    ((receivedConstraintMap (R := ZMod q) (d := d) m alpha y).domRestrict
      (interpolationSpace q d m A K B W C))
    (fun Q => by
      change receivedConstraintMap (d := d) m alpha y Q.1 ∈
        coupledContactEnvelopeSpace (R := ZMod q) (d := d) m W
      rw [receivedConstraintMap_eq_localConstraintMap_translatedTruncation]
      apply localConstraintMap_mem_coupledContactEnvelopeSpace
      exact translatedTruncation_mem_localVSpace Q.2 alpha y)

@[simp]
theorem coupledPointConstraintMap_coe {q d m A K B W C : ℕ}
    (alpha y : ZMod q) (Q : interpolationSpace q d m A K B W C) :
    (coupledPointConstraintMap alpha y Q : LocalPolynomial (ZMod q) d) =
      receivedConstraintMap (d := d) m alpha y Q.1 := rfl

theorem coupledPointConstraintMap_eq_zero_iff_satisfiesLocalConstraints
    {q d m A K B W C : ℕ}
    (alpha y : ZMod q) (Q : interpolationSpace q d m A K B W C) :
    coupledPointConstraintMap alpha y Q = 0 ↔
      SatisfiesLocalConstraints m alpha y Q.1 := by
  rw [satisfiesLocalConstraints_iff_receivedConstraintMap_eq_zero]
  constructor
  · intro h
    have := congrArg
      (fun F : coupledContactEnvelopeSpace
          (R := ZMod q) (d := d) m W =>
        (F.1 : LocalPolynomial (ZMod q) d)) h
    simpa using this
  · intro h
    apply Subtype.ext
    simpa using h

/-- Common-kernel theorem using the exact coupled local envelope. -/
theorem exists_nonzero_interpolant_satisfying_constraints_coupled
    {q d m A K B W C n : ℕ} [Fact (Nat.Prime q)]
    (hd : 0 < d)
    (hdim :
      n * Module.finrank (ZMod q)
          (coupledContactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C))
    (alpha y : Fin n → ZMod q) :
    ∃ Q : DifferentialPolynomial q d,
      Q ≠ 0 ∧ Q ∈ interpolationSpace q d m A K B W C ∧
      ∀ i : Fin n, SatisfiesLocalConstraints m (alpha i) (y i) Q := by
  let sourceBasis := interpolationSpaceBasis q d m A K B W C
  letI : Module.Finite (ZMod q)
      (interpolationSpace q d m A K B W C) :=
    Module.Finite.of_basis sourceBasis
  let code :
      {e : LocalVariable d →₀ ℕ //
        CoupledContactEnvelopeExponent (d := d) m W e} →
        CoupledContactEnvelopeCode d m W := encodeCoupledContactEnvelope hd
  letI : Fintype
      {e : LocalVariable d →₀ ℕ //
        CoupledContactEnvelopeExponent (d := d) m W e} :=
    Fintype.ofInjective code (by
      simpa [code] using
        encodeCoupledContactEnvelope_injective (m := m) (W := W) hd)
  let targetBasis : Module.Basis
      {e : LocalVariable d →₀ ℕ //
        CoupledContactEnvelopeExponent (d := d) m W e}
      (ZMod q)
      (coupledContactEnvelopeSpace (R := ZMod q) (d := d) m W) :=
    MvPolynomial.basisRestrictSupport (ZMod q)
      {e | CoupledContactEnvelopeExponent (d := d) m W e}
  letI : Module.Finite (ZMod q)
      (coupledContactEnvelopeSpace (R := ZMod q) (d := d) m W) :=
    Module.Finite.of_basis targetBasis
  obtain ⟨Q, hQne, hQconstraints⟩ :=
    exists_ne_zero_forall_apply_eq_zero
      (F := ZMod q) (ι := Fin n)
      (fun i => coupledPointConstraintMap (alpha i) (y i))
      (by simpa using hdim)
  refine ⟨Q.1, ?_, Q.2, fun i => ?_⟩
  · intro hzero
    apply hQne
    apply Subtype.ext
    exact hzero
  · exact (coupledPointConstraintMap_eq_zero_iff_satisfiesLocalConstraints
      (alpha i) (y i) Q).mp (hQconstraints i)

/-- The point constraint with both signed rewrite invariants retained. -/
def sharpenedPointConstraintMap {q d m A K B W C : ℕ}
    (alpha y : ZMod q) :
    interpolationSpace q d m A K B W C →ₗ[ZMod q]
      sharpenedContactEnvelopeSpace (R := ZMod q) (d := d) m W :=
  LinearMap.codRestrict
    (sharpenedContactEnvelopeSpace (R := ZMod q) (d := d) m W)
    ((receivedConstraintMap (R := ZMod q) (d := d) m alpha y).domRestrict
      (interpolationSpace q d m A K B W C))
    (fun Q => by
      change receivedConstraintMap (d := d) m alpha y Q.1 ∈
        sharpenedContactEnvelopeSpace (R := ZMod q) (d := d) m W
      rw [receivedConstraintMap_eq_localConstraintMap_translatedTruncation]
      apply localConstraintMap_mem_sharpenedContactEnvelopeSpace
      exact translatedTruncation_mem_localVSpace Q.2 alpha y)

@[simp]
theorem sharpenedPointConstraintMap_coe {q d m A K B W C : ℕ}
    (alpha y : ZMod q) (Q : interpolationSpace q d m A K B W C) :
    (sharpenedPointConstraintMap alpha y Q : LocalPolynomial (ZMod q) d) =
      receivedConstraintMap (d := d) m alpha y Q.1 := rfl

theorem sharpenedPointConstraintMap_eq_zero_iff_satisfiesLocalConstraints
    {q d m A K B W C : ℕ}
    (alpha y : ZMod q) (Q : interpolationSpace q d m A K B W C) :
    sharpenedPointConstraintMap alpha y Q = 0 ↔
      SatisfiesLocalConstraints m alpha y Q.1 := by
  rw [satisfiesLocalConstraints_iff_receivedConstraintMap_eq_zero]
  constructor
  · intro h
    have := congrArg
      (fun F : sharpenedContactEnvelopeSpace
          (R := ZMod q) (d := d) m W =>
        (F.1 : LocalPolynomial (ZMod q) d)) h
    simpa using this
  · intro h
    apply Subtype.ext
    simpa using h

/-- Common-kernel theorem for the sharpened support-only local count. -/
theorem exists_nonzero_interpolant_satisfying_constraints_sharpened
    {q d m A K B W C n : ℕ} [Fact (Nat.Prime q)]
    (hd : 0 < d)
    (hdim :
      n * Module.finrank (ZMod q)
          (sharpenedContactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C))
    (alpha y : Fin n → ZMod q) :
    ∃ Q : DifferentialPolynomial q d,
      Q ≠ 0 ∧ Q ∈ interpolationSpace q d m A K B W C ∧
      ∀ i : Fin n, SatisfiesLocalConstraints m (alpha i) (y i) Q := by
  let sourceBasis := interpolationSpaceBasis q d m A K B W C
  letI : Module.Finite (ZMod q)
      (interpolationSpace q d m A K B W C) :=
    Module.Finite.of_basis sourceBasis
  let code :
      {e : LocalVariable d →₀ ℕ //
        SharpenedContactEnvelopeExponent (d := d) m W e} →
        SharpenedContactEnvelopeCode d m W :=
    encodeSharpenedContactEnvelope hd
  letI : Fintype
      {e : LocalVariable d →₀ ℕ //
        SharpenedContactEnvelopeExponent (d := d) m W e} :=
    Fintype.ofInjective code (by
      simpa [code] using
        encodeSharpenedContactEnvelope_injective (m := m) (W := W) hd)
  let targetBasis : Module.Basis
      {e : LocalVariable d →₀ ℕ //
        SharpenedContactEnvelopeExponent (d := d) m W e}
      (ZMod q)
      (sharpenedContactEnvelopeSpace (R := ZMod q) (d := d) m W) :=
    MvPolynomial.basisRestrictSupport (ZMod q)
      {e | SharpenedContactEnvelopeExponent (d := d) m W e}
  letI : Module.Finite (ZMod q)
      (sharpenedContactEnvelopeSpace (R := ZMod q) (d := d) m W) :=
    Module.Finite.of_basis targetBasis
  obtain ⟨Q, hQne, hQconstraints⟩ :=
    exists_ne_zero_forall_apply_eq_zero
      (F := ZMod q) (ι := Fin n)
      (fun i => sharpenedPointConstraintMap (alpha i) (y i))
      (by simpa using hdim)
  refine ⟨Q.1, ?_, Q.2, fun i => ?_⟩
  · intro hzero
    apply hQne
    apply Subtype.ext
    exact hzero
  · exact (sharpenedPointConstraintMap_eq_zero_iff_satisfiesLocalConstraints
      (alpha i) (y i) Q).mp (hQconstraints i)

/-- Fully discrete existence theorem: a shell ratio and the final scalar
comparison imply a common nonzero interpolant. -/
theorem exists_nonzero_interpolant_of_shell
    {q d A K B W C H R n : ℕ} [Fact (Nat.Prime q)]
    (hd : 0 < d)
    (hH : H ≤ d ^ 3) (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ d ^ 3 * A)
    (hshell : scaledExponentCount d (W + d ^ 3) ≤
      R * goodScaledExponentCount d W C)
    (harithmetic : n * (4 * d ^ 8 * R) < (K - 1) * H ^ 3)
    (alpha y : Fin n → ZMod q) :
    ∃ Q : DifferentialPolynomial q d,
      Q ≠ 0 ∧ Q ∈ interpolationSpace q d (d ^ 3) A K B W C ∧
      ∀ i : Fin n, SatisfiesLocalConstraints (d ^ 3) (alpha i) (y i) Q := by
  apply exists_nonzero_interpolant_satisfying_constraints hd _ alpha y
  exact total_contactEnvelope_finrank_lt_interpolationSpace
    hd hH hdegree hweighted hshell harithmetic

end RSListDecoding
