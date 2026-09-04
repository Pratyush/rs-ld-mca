import RSListDecoding.Lemmas.InterpolationKernel
import RSListDecoding.Lemmas.InterpolationVanishing
import RSListDecoding.Lemmas.RankArithmetic
import RSListDecoding.Lemmas.ScaledShell
import RSListDecoding.Lemmas.ScopedGlobalDimension

/-!
# Construction of the ambient explainer

This module assembles the proof at fixed rounded parameters.  The repaired
scaled-shell estimate controls the total local constraint dimension, the
rectangular monomial family controls the global interpolation dimension, and
the common-kernel argument produces a nonzero interpolant.  Contact and the
global degree budget then show that every ambient decoding-list candidate
satisfies the resulting differential equation.
-/

noncomputable section

namespace RSListDecoding

/-- At fixed parameters, the repaired shell estimate and the honest floor
bound for the interpolation box produce exactly the explainer consumed by the
root-counting reduction. -/
theorem exists_scoped_ambient_explainer
    {ε θ : ℝ} {n q : ℕ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hn : 0 < n)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n)
    (hsmall : ε < repairedRankEpsilonBound θ)
    (hq : Nat.Prime q)
    (hshell :
      scaledExponentCount (derivativeOrder ε θ)
          (interpolationWeightBudget ε θ + multiplicity ε θ) ≤
        scaledShellFactor θ (derivativeOrder ε θ) *
          goodScaledExponentCount (derivativeOrder ε θ)
            (interpolationWeightBudget ε θ)
            (higherJetDegreeBudget ε θ))
    (hfactor :
      (scaledShellFactor θ (derivativeOrder ε θ) : ℝ) ≤
        2 * (derivativeOrder ε θ : ℝ) ^ scaledShellExponent θ)
    (hbox : 2 ≤ θ * (multiplicity ε θ : ℝ) / 16)
    (alpha : Fin n → ZMod q) (halpha : Function.Injective alpha)
    (y : Fin n → ZMod q) :
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
          (messagePolynomialAtDimension (Nat.zero_lt_of_lt hdK) p) = 0 := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hd : 0 < derivativeOrder ε θ := derivativeOrder_pos θ hε
  have hwidth :
      θ * (multiplicity ε θ : ℝ) / 32 ≤
        (interpolationBoxWidth ε θ : ℝ) :=
    half_interpolationBoxWidthTarget_le_cast hbox
  have hfactor' :
      (scaledShellFactor θ (derivativeOrder ε θ) : ℝ) ≤
        2 * (derivativeOrder ε θ : ℝ) ^ shellExponent θ := by
    simpa [scaledShellExponent, shellExponent] using hfactor
  have hcompare := one_lt_repaired_rank_coefficient
    hε hε₁ hθ hθ₁ hsmall hdK
  have harithmetic :
      n * (4 * derivativeOrder ε θ ^ 8 *
          scaledShellFactor θ (derivativeOrder ε θ)) <
        (ambientDimension ε θ n - 1) *
          interpolationBoxWidth ε θ ^ 3 :=
    contactEnvelope_scalar_lt_globalRectangle
      hθ hd hn hwidth hfactor' hcompare
  obtain ⟨hH, hdegree, hweighted⟩ :=
    roundedGlobalDimensionSlacks hε hθ hθ₁ hn hdK
  have hinterpolant :
      ∃ Q : DifferentialPolynomial q (derivativeOrder ε θ),
        Q ≠ 0 ∧
        Q ∈ interpolationSpace q
          (derivativeOrder ε θ) (multiplicity ε θ)
          (agreementThreshold ε n) (ambientDimension ε θ n)
          (interpolationDegreeBudget ε θ n)
          (interpolationWeightBudget ε θ)
          (higherJetDegreeBudget ε θ) ∧
        ∀ i : Fin n,
          SatisfiesLocalConstraints (multiplicity ε θ)
            (alpha i) (y i) Q := by
    simpa only [multiplicity] using
      exists_nonzero_interpolant_of_shell
        (q := q) (A := agreementThreshold ε n)
        (K := ambientDimension ε θ n)
        (B := interpolationDegreeBudget ε θ n)
        (W := interpolationWeightBudget ε θ)
        (C := higherJetDegreeBudget ε θ)
        (H := interpolationBoxWidth ε θ)
        (R := scaledShellFactor θ (derivativeOrder ε θ))
        hd hH hdegree hweighted hshell harithmetic alpha y
  exact exists_ambient_explainer_of_nonzero_interpolant
    hq (Nat.zero_lt_of_lt hdK)
      (Nat.mul_pos (multiplicity_pos θ hε)
        (agreementThreshold_pos hε hn))
      alpha halpha y hinterpolant

end RSListDecoding
