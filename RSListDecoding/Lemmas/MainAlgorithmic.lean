import RSListDecoding.Lemmas.MainCombinatorial
import RSListDecoding.Lemmas.RuntimeBounds

/-!
# Algorithmic Reed--Solomon list decoding

This file assembles the checked interpolation matrix construction, the checked
Gaussian kernel solver, the externally supplied Kopparty root enumerator, and
the checked final filter.  Complexity is measured solely in base-field
operations by FieldCost.
-/

noncomputable section

namespace RSListDecoding

/-- The rank inequality used by the algorithmic interpolation solver, at the
rounded public parameters. -/
theorem scoped_interpolation_dimension_lt
    {ε θ : ℝ} {n q : ℕ} [Fact (Nat.Prime q)]
    (hε : 0 < ε) (hε₁ : ε < 1) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hn : 0 < n)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n)
    (hsmall : ε < repairedRankEpsilonBound θ)
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
    (hbox : 2 ≤ θ * (multiplicity ε θ : ℝ) / 16) :
    n * Module.finrank (ZMod q)
        (contactEnvelopeSpace (R := ZMod q)
          (d := derivativeOrder ε θ)
          (multiplicity ε θ) (interpolationWeightBudget ε θ)) <
      Module.finrank (ZMod q)
        (interpolationSpace q
          (derivativeOrder ε θ) (multiplicity ε θ)
          (agreementThreshold ε n) (ambientDimension ε θ n)
          (interpolationDegreeBudget ε θ n)
          (interpolationWeightBudget ε θ)
          (higherJetDegreeBudget ε θ)) := by
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
  unfold multiplicity
  exact total_contactEnvelope_finrank_lt_interpolationSpace
      (q := q) (A := agreementThreshold ε n)
      (K := ambientDimension ε θ n)
      (B := interpolationDegreeBudget ε θ n)
      (W := interpolationWeightBudget ε θ)
      (C := higherJetDegreeBudget ε θ)
      (H := interpolationBoxWidth ε θ)
      (R := scaledShellFactor θ (derivativeOrder ε θ))
      hd hH hdegree hweighted hshell harithmetic

/-- The exact algorithmic statement selected in FORMALIZATION_SCOPE.md. -/
theorem algorithmicMainStatement_proved : AlgorithmicMainStatement := by
  let cRoot := kopparty_theorem_4_3_algorithm.exponentConstant
  refine ⟨cRoot + 34, by
    have := kopparty_theorem_4_3_algorithm.exponentConstant_pos
    omega, ?_⟩
  intro θ hθ hθ₁
  obtain ⟨dShell, hShell⟩ :=
    exists_scaledShellThreshold_for_roundedParameters hθ hθ₁
  obtain ⟨dBox, hBox⟩ :=
    exists_derivativeOrderThreshold_for_boxWidth hθ
  let D := max dShell dBox
  obtain ⟨ε₀, hε₀, hε₀one, hε₀paper, hε₀rank, hthreshold⟩ :=
    exists_epsilonZero_below_with_derivativeOrder_threshold
      hθ hθ₁ (repairedRankEpsilonBound_pos hθ hθ₁) D
  refine ⟨ε₀, hε₀, hε₀one, ?_, ?_⟩
  · simpa [manuscriptEpsilonBound] using hε₀paper
  · intro ε hε hεε₀ n hn hdK k q _hk hkK hq hnq hBq hMq alpha halpha
    have hε₁ : ε < 1 := hεε₀.trans_le hε₀one
    have hnpos : 0 < n := by omega
    have hD : D ≤ derivativeOrder ε θ := hthreshold ε hε hεε₀
    have hdShell : dShell ≤ derivativeOrder ε θ :=
      (Nat.le_max_left dShell dBox).trans hD
    have hdBox : dBox ≤ derivativeOrder ε θ :=
      (Nat.le_max_right dShell dBox).trans hD
    obtain ⟨_hbad, _hratio, hshell, hfactor⟩ :=
      hShell ε hε hdShell
    have hbox :
        2 ≤ θ * (multiplicity ε θ : ℝ) / 16 := by
      simpa only [multiplicity] using
        hBox (derivativeOrder ε θ) hdBox
    have hsmall : ε < repairedRankEpsilonBound θ :=
      hεε₀.trans_le hε₀rank
    have hd : 0 < derivativeOrder ε θ := derivativeOrder_pos θ hε
    have hKn : ambientDimension ε θ n < n :=
      ambientDimension_lt_blockLength hε hε₁ hθ hθ₁ hnpos
    have hB : 0 < interpolationDegreeBudget ε θ n :=
      interpolationDegreeBudget_pos hε hnpos hdK
    have hmA :
        0 < multiplicity ε θ * agreementThreshold ε n :=
      Nat.mul_pos (multiplicity_pos θ hε)
        (agreementThreshold_pos hε hnpos)
    letI : Fact (Nat.Prime q) := ⟨hq⟩
    have hdim := scoped_interpolation_dimension_lt
      (q := q) hε hε₁ hθ hθ₁ hnpos hdK hsmall hshell hfactor hbox
    have hW :
        interpolationWeightBudget ε θ ≤
          2 * derivativeOrder ε θ ^ 4 :=
      interpolationWeightBudget_le_two_mul_derivativeOrder_pow_four
        hθ hθ₁ hd
    let decode : (Fin n → ZMod q) →
        FieldCost (Finset (Message q k)) :=
      fun y ↦ decoderProgram hq hd hdK hB hkK hmA hMq hBq hdim alpha y
    refine ⟨decode, ?_⟩
    intro y
    have hcorrect :
        (decode y).result =
          decodingList (k := k) hq.ne_zero alpha y
            (agreementThreshold ε n) := by
      dsimp [decode]
      exact decoderProgram_result_eq_decodingList
        hq hd hdK hB hkK hmA hMq hBq hdim alpha halpha y
    have hlist :
        IsListDecodableAtAgreement (k := k) hq.ne_zero alpha
          (agreementThreshold ε n) (publicListBound q ε θ) := by
      apply scoped_list_bound_of_ambient_explainers
        hε hε₁ hθ hθ₁ hnpos hdK hkK hq hnq hBq hMq alpha
      intro received
      exact exists_scoped_ambient_explainer
        hε hε₁ hθ hθ₁ hnpos hdK hsmall hq hshell hfactor hbox
          alpha halpha received
    have hcostLinear :
        (decode y).operations ≤
          q ^ ((cRoot + 34) * (derivativeOrder ε θ + 1)) := by
      dsimp [decode, cRoot]
      simpa only [multiplicity] using
        decoderProgram_operations_le_q_pow
          hq hd hdK hKn hnq hB hkK hmA hMq hBq hW hdim alpha y
    have hdle4 :
        derivativeOrder ε θ ≤ derivativeOrder ε θ ^ 4 := by
      simpa using Nat.pow_le_pow_right hd (by omega : 1 ≤ 4)
    have hcost :
        (decode y).operations ≤
          q ^ ((cRoot + 34) * (derivativeOrder ε θ ^ 4 + 1)) :=
      hcostLinear.trans (Nat.pow_le_pow_right hq.pos
        (Nat.mul_le_mul_left _ (by omega)))
    exact ⟨hcorrect, hcorrect ▸ hlist y, hcost⟩

end RSListDecoding
