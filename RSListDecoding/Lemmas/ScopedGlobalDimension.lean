import RSListDecoding.Lemmas.GlobalDimension
import RSListDecoding.Lemmas.Parameters
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Global interpolation dimension at the rounded parameters

This file specializes the discrete rectangular lower bound from
`GlobalDimension` to the rounded parameters used by the combinatorial
theorem.  The three slack hypotheses of the generic bound are discharged
here, so later interpolation modules do not have to unfold floors and
ceilings.

The final lemma also records a quantitative lower bound on the rectangular
width.  Its explicit large-parameter hypothesis keeps the loss from taking a
natural floor honest.
-/

noncomputable section

namespace RSListDecoding

/-- The rectangular width is at most the multiplicity. -/
theorem interpolationBoxWidth_le_multiplicity {ε θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) :
    interpolationBoxWidth ε θ ≤ multiplicity ε θ := by
  have hH := interpolationBoxWidth_cast_le (ε := ε) hθ.le
  have hm : 0 ≤ (multiplicity ε θ : ℝ) := by positivity
  have hθsixteen : θ / 16 ≤ 1 := by linarith
  have hreal :
      (interpolationBoxWidth ε θ : ℝ) ≤
        (multiplicity ε θ : ℝ) := by
    calc
      (interpolationBoxWidth ε θ : ℝ) ≤
          θ * (multiplicity ε θ : ℝ) / 16 := hH
      _ = (θ / 16) * (multiplicity ε θ : ℝ) := by ring
      _ ≤ 1 * (multiplicity ε θ : ℝ) :=
        mul_le_mul_of_nonneg_right hθsixteen hm
      _ = (multiplicity ε θ : ℝ) := one_mul _
  exact_mod_cast hreal

/-- The ordinary higher-jet cutoff and two rectangular coordinates fit in
the rounded individual jet-degree budget. -/
theorem higherJetDegreeBudget_add_two_boxWidth_le_interpolationDegreeBudget
    {ε θ : ℝ} {n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) (hn : 0 < n)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    higherJetDegreeBudget ε θ + 2 * interpolationBoxWidth ε θ ≤
      interpolationDegreeBudget ε θ n := by
  apply le_interpolationDegreeBudget_of_mul_denominator_lt hε hdK
  calc
    (higherJetDegreeBudget ε θ + 2 * interpolationBoxWidth ε θ) *
          (ambientDimension ε θ n - 1) =
        (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudget ε θ + 2 * interpolationBoxWidth ε θ) := by
            ac_rfl
    _ ≤ (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudget ε θ + 3 * interpolationBoxWidth ε θ) := by
            gcongr
            omega
    _ < multiplicity ε θ * agreementThreshold ε n :=
      boxFamily_weightedBudget_lt hε hθ hθ₁ hn

/-- The weighted-degree slack needed by the rectangular family, in the weak
form expected by `finrank_interpolationSpace_lowerBound`. -/
theorem boxFamily_weightedBudget_le
    {ε θ : ℝ} {n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) (hn : 0 < n) :
    (ambientDimension ε θ n - 1) *
        (higherJetDegreeBudget ε θ + 3 * interpolationBoxWidth ε θ) ≤
      multiplicity ε θ * agreementThreshold ε n :=
  (boxFamily_weightedBudget_lt hε hθ hθ₁ hn).le

/-- All three arithmetic hypotheses of the generic rectangular dimension
bound, collected at the rounded parameters. -/
theorem roundedGlobalDimensionSlacks
    {ε θ : ℝ} {n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) (hn : 0 < n)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    interpolationBoxWidth ε θ ≤ multiplicity ε θ ∧
      higherJetDegreeBudget ε θ + 2 * interpolationBoxWidth ε θ ≤
        interpolationDegreeBudget ε θ n ∧
      (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudget ε θ + 3 * interpolationBoxWidth ε θ) ≤
        multiplicity ε θ * agreementThreshold ε n := by
  exact ⟨interpolationBoxWidth_le_multiplicity hθ hθ₁,
    higherJetDegreeBudget_add_two_boxWidth_le_interpolationDegreeBudget
      hε hθ hθ₁ hn hdK,
    boxFamily_weightedBudget_le hε hθ hθ₁ hn⟩

/-- The global interpolation space has the discrete rectangular dimension
lower bound at exactly the rounded parameters from the capstone. -/
theorem finrank_scopedInterpolationSpace_lowerBound
    {q : ℕ} {ε θ : ℝ} {n : ℕ} [Fact (1 < q)]
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) (hn : 0 < n)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    (goodHigherExponents
          (derivativeOrder ε θ)
          (interpolationWeightBudget ε θ)
          (higherJetDegreeBudget ε θ)).card *
        (ambientDimension ε θ n - 1) *
        interpolationBoxWidth ε θ ^ 3 ≤
      Module.finrank (ZMod q)
        (interpolationSpace q
          (derivativeOrder ε θ)
          (multiplicity ε θ)
          (agreementThreshold ε n)
          (ambientDimension ε θ n)
          (interpolationDegreeBudget ε θ n)
          (interpolationWeightBudget ε θ)
          (higherJetDegreeBudget ε θ)) := by
  obtain ⟨hH, hdegree, hweighted⟩ :=
    roundedGlobalDimensionSlacks hε hθ hθ₁ hn hdK
  exact finrank_interpolationSpace_lowerBound
    (Nat.succ_le_iff.mpr (derivativeOrder_pos θ hε))
    hH hdegree hweighted

/-- Once the unrounded width is at least two, taking its natural floor loses
at most a factor of two. -/
theorem half_interpolationBoxWidthTarget_le_cast
    {ε θ : ℝ}
    (hlarge : 2 ≤ θ * (multiplicity ε θ : ℝ) / 16) :
    θ * (multiplicity ε θ : ℝ) / 32 ≤
      (interpolationBoxWidth ε θ : ℝ) := by
  have hfloor := Nat.div_two_lt_floor
    (a := θ * (multiplicity ε θ : ℝ) / 16) (by linarith)
  rw [interpolationBoxWidth]
  calc
    θ * (multiplicity ε θ : ℝ) / 32 =
        (θ * (multiplicity ε θ : ℝ) / 16) / 2 := by ring
    _ ≤ (⌊θ * (multiplicity ε θ : ℝ) / 16⌋₊ : ℝ) := hfloor.le

end RSListDecoding
