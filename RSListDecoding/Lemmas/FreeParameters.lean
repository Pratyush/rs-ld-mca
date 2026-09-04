import RSListDecoding.Lemmas.Parameters
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Rounded parameters at a free derivative order

The manuscript sets `d = ceil (ε^(-3/θ))`.  None of the discrete
interpolation, contact, or root-counting arguments requires that identity.
This file proves the rounded budget facts with `d` supplied independently.
-/

noncomputable section

namespace RSListDecoding

theorem multiplicityAt_pos {d : ℕ} (hd : 0 < d) :
    0 < multiplicityAt d := by
  simp [multiplicityAt, hd]

theorem blockLength_pos_of_order_lt_ambientDimension
    {ε θ : ℝ} {d n : ℕ}
    (hdK : d < ambientDimension ε θ n) :
    0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  simp [ambientDimension] at hdK

theorem interpolationDenominatorAt_pos
    {ε θ : ℝ} {d n : ℕ} (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n) :
    0 < ambientDimension ε θ n - 1 := by
  have hK : 1 < ambientDimension ε θ n :=
    lt_of_le_of_lt hd hdK
  omega

theorem interpolationDegreeBudgetAt_pos
    {ε θ : ℝ} {d n : ℕ} (hε : 0 < ε) (hd : 0 < d) (hn : 0 < n)
    (hdK : d < ambientDimension ε θ n) :
    0 < interpolationDegreeBudgetAt d ε θ n := by
  rw [interpolationDegreeBudgetAt, Nat.ceil_pos]
  apply div_pos
  · exact_mod_cast Nat.mul_pos (multiplicityAt_pos hd)
      (agreementThreshold_pos hε hn)
  · exact_mod_cast interpolationDenominatorAt_pos hd hdK

theorem multiplicityAt_mul_agreementThreshold_le_budget_mul_denominator
    {ε θ : ℝ} {d n : ℕ} (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n) :
    multiplicityAt d * agreementThreshold ε n ≤
      interpolationDegreeBudgetAt d ε θ n *
        (ambientDimension ε θ n - 1) := by
  have hdenNat : 0 < ambientDimension ε θ n - 1 :=
    interpolationDenominatorAt_pos hd hdK
  have hdenReal : 0 < ((ambientDimension ε θ n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hdenNat
  have hceil :
      (((multiplicityAt d * agreementThreshold ε n : ℕ) : ℝ) /
          ((ambientDimension ε θ n - 1 : ℕ) : ℝ)) ≤
        (interpolationDegreeBudgetAt d ε θ n : ℝ) := by
    simpa [interpolationDegreeBudgetAt] using
      Nat.le_ceil
        (((multiplicityAt d * agreementThreshold ε n : ℕ) : ℝ) /
          ((ambientDimension ε θ n - 1 : ℕ) : ℝ))
  have hreal :
      ((multiplicityAt d * agreementThreshold ε n : ℕ) : ℝ) ≤
        (interpolationDegreeBudgetAt d ε θ n : ℝ) *
          ((ambientDimension ε θ n - 1 : ℕ) : ℝ) :=
    (div_le_iff₀ hdenReal).mp hceil
  exact_mod_cast hreal

theorem higherJetDegreeBudgetAt_cast_le {θ : ℝ} {d : ℕ}
    (hθ : 0 ≤ θ) :
    (higherJetDegreeBudgetAt θ d : ℝ) ≤
      (1 + 3 * θ / 4) * (multiplicityAt d : ℝ) := by
  rw [higherJetDegreeBudgetAt]
  apply Nat.floor_le
  positivity

theorem interpolationBoxWidthAt_cast_le {θ : ℝ} {d : ℕ}
    (hθ : 0 ≤ θ) :
    (interpolationBoxWidthAt θ d : ℝ) ≤
      θ * (multiplicityAt d : ℝ) / 12 := by
  rw [interpolationBoxWidthAt]
  apply Nat.floor_le
  positivity

theorem interpolationSimplexWidthAt_cast_le {θ : ℝ} {d : ℕ}
    (hθ : 0 ≤ θ) :
    (interpolationSimplexWidthAt θ d : ℝ) ≤
      θ * (multiplicityAt d : ℝ) / 4 := by
  rw [interpolationSimplexWidthAt]
  apply Nat.floor_le
  positivity

theorem optimizedSimplexSlackCoefficient_pos
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    0 < optimizedSimplexSlackCoefficient θ := by
  unfold optimizedSimplexSlackCoefficient
  exact lt_min (by norm_num) (by positivity)

theorem optimizedSimplexSlackCoefficient_le_one (θ : ℝ) :
    optimizedSimplexSlackCoefficient θ ≤ 1 := by
  unfold optimizedSimplexSlackCoefficient
  exact min_le_left _ _

theorem optimizedSimplexSlackCoefficient_le_rateSlack (θ : ℝ) :
    optimizedSimplexSlackCoefficient θ ≤
      θ * (1 + 3 * θ) / (4 * (1 - θ)) := by
  unfold optimizedSimplexSlackCoefficient
  exact min_le_right _ _

/-- The maximal coefficient always improves on the former `θ/4` choice. -/
theorem theta_div_four_le_optimizedSimplexSlackCoefficient
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    θ / 4 ≤ optimizedSimplexSlackCoefficient θ := by
  rw [optimizedSimplexSlackCoefficient, le_min_iff]
  constructor
  · linarith
  · rw [le_div_iff₀ (by positivity : 0 < 4 * (1 - θ))]
    nlinarith [sq_nonneg θ]

theorem theta_div_four_lt_optimizedSimplexSlackCoefficient
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    θ / 4 < optimizedSimplexSlackCoefficient θ := by
  rw [optimizedSimplexSlackCoefficient, lt_min_iff]
  constructor
  · linarith
  · rw [lt_div_iff₀ (by positivity : 0 < 4 * (1 - θ))]
    nlinarith [sq_pos_of_pos hθ]

/-- The old `θ³/384` volume coefficient is strictly dominated for every
`0 < θ < 1`. -/
theorem theta_cube_div_384_lt_optimizedSimplexVolumeCoefficient
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    θ ^ 3 / 384 < optimizedSimplexVolumeCoefficient θ := by
  have hcoeff := theta_div_four_lt_optimizedSimplexSlackCoefficient hθ hθ₁
  have hpow : (θ / 4) ^ 3 <
      optimizedSimplexSlackCoefficient θ ^ 3 := by
    exact pow_lt_pow_left₀ hcoeff (by positivity) (by omega)
  rw [optimizedSimplexVolumeCoefficient]
  nlinarith

/-- The optimized simplex coefficient exactly fills the uniform rate slack,
unless it is capped by the multiplicity-coordinate constraint. -/
theorem higherJetCoefficient_add_optimizedSlack_le_rateInverse
    {θ : ℝ} (_hθ : 0 < θ) (hθ₁ : θ < 1) :
    1 + 3 * θ / 4 + optimizedSimplexSlackCoefficient θ ≤
      1 / (1 - θ) := by
  have hCoeff := optimizedSimplexSlackCoefficient_le_rateSlack θ
  calc
    1 + 3 * θ / 4 + optimizedSimplexSlackCoefficient θ ≤
        1 + 3 * θ / 4 +
          θ * (1 + 3 * θ) / (4 * (1 - θ)) := by linarith
    _ = 1 / (1 - θ) := by
      field_simp [ne_of_gt (sub_pos.mpr hθ₁)]
      ring

theorem optimizedInterpolationSimplexWidthAt_cast_le
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) {d : ℕ} :
    (optimizedInterpolationSimplexWidthAt θ d : ℝ) ≤
      optimizedSimplexSlackCoefficient θ * (multiplicityAt d : ℝ) := by
  rw [optimizedInterpolationSimplexWidthAt]
  apply Nat.floor_le
  exact mul_nonneg
    (optimizedSimplexSlackCoefficient_pos hθ hθ₁).le (by positivity)

/-- The directly rounded maximal width contains the former simplex. -/
theorem interpolationSimplexWidthAt_le_optimized
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) {d : ℕ} :
    interpolationSimplexWidthAt θ d ≤
      optimizedInterpolationSimplexWidthAt θ d := by
  rw [optimizedInterpolationSimplexWidthAt]
  apply Nat.le_floor
  have hold := interpolationSimplexWidthAt_cast_le (d := d) hθ.le
  have hcoefficient :=
    theta_div_four_le_optimizedSimplexSlackCoefficient hθ hθ₁
  calc
    (interpolationSimplexWidthAt θ d : ℝ) ≤
        θ * (multiplicityAt d : ℝ) / 4 := hold
    _ = (θ / 4) * (multiplicityAt d : ℝ) := by ring
    _ ≤ optimizedSimplexSlackCoefficient θ *
        (multiplicityAt d : ℝ) := by gcongr

theorem three_interpolationBoxWidthAt_le_simplexWidthAt
    {θ : ℝ} {d : ℕ} (hθ : 0 ≤ θ) :
    3 * interpolationBoxWidthAt θ d ≤
      interpolationSimplexWidthAt θ d := by
  rw [interpolationSimplexWidthAt]
  apply Nat.le_floor
  have hH := interpolationBoxWidthAt_cast_le (d := d) hθ
  push_cast
  nlinarith

theorem higherJetDegreeBudgetAt_add_three_boxWidthAt_cast_le
    {θ : ℝ} {d : ℕ} (hθ : 0 ≤ θ) :
    ((higherJetDegreeBudgetAt θ d +
        3 * interpolationBoxWidthAt θ d : ℕ) : ℝ) ≤
      (1 + θ) * (multiplicityAt d : ℝ) := by
  push_cast
  have hC := higherJetDegreeBudgetAt_cast_le (d := d) hθ
  have hH := interpolationBoxWidthAt_cast_le (d := d) hθ
  nlinarith

theorem higherJetDegreeBudgetAt_add_simplexWidthAt_cast_le
    {θ : ℝ} {d : ℕ} (hθ : 0 ≤ θ) :
    ((higherJetDegreeBudgetAt θ d +
        interpolationSimplexWidthAt θ d : ℕ) : ℝ) ≤
      (1 + θ) * (multiplicityAt d : ℝ) := by
  push_cast
  have hC := higherJetDegreeBudgetAt_cast_le (d := d) hθ
  have hJ := interpolationSimplexWidthAt_cast_le (d := d) hθ
  nlinarith

/-- The optimized simplex fills all uniform degree/rate slack left by the
current higher-jet cutoff. -/
theorem higherJetDegreeBudgetAt_add_optimizedSimplexWidthAt_cast_le
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) {d : ℕ} :
    ((higherJetDegreeBudgetAt θ d +
        optimizedInterpolationSimplexWidthAt θ d : ℕ) : ℝ) ≤
      (1 / (1 - θ)) * (multiplicityAt d : ℝ) := by
  norm_num only [Nat.cast_add]
  have hC := higherJetDegreeBudgetAt_cast_le (d := d) hθ.le
  have hJ := optimizedInterpolationSimplexWidthAt_cast_le hθ hθ₁ (d := d)
  have hsum :=
    higherJetCoefficient_add_optimizedSlack_le_rateInverse hθ hθ₁
  calc
    (higherJetDegreeBudgetAt θ d : ℝ) +
        (optimizedInterpolationSimplexWidthAt θ d : ℝ) ≤
      (1 + 3 * θ / 4) * (multiplicityAt d : ℝ) +
        optimizedSimplexSlackCoefficient θ *
          (multiplicityAt d : ℝ) := add_le_add hC hJ
    _ = (1 + 3 * θ / 4 + optimizedSimplexSlackCoefficient θ) *
        (multiplicityAt d : ℝ) := by ring
    _ ≤ (1 / (1 - θ)) * (multiplicityAt d : ℝ) := by gcongr

/-- Weighted-budget estimate for a single shared slack parameter. -/
theorem simplexFamilyAt_weightedBudget_lt
    {ε θ : ℝ} {d n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hd : 0 < d) (hn : 0 < n) :
    (ambientDimension ε θ n - 1) *
        (higherJetDegreeBudgetAt θ d +
          interpolationSimplexWidthAt θ d) <
      multiplicityAt d * agreementThreshold ε n := by
  have hfactor : (1 - θ) * (1 + θ) < 1 := by
    nlinarith [mul_pos hθ (sub_pos.mpr hθ₁)]
  have hm : 0 < (multiplicityAt d : ℝ) := by
    exact_mod_cast multiplicityAt_pos hd
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hxnonneg : 0 ≤ (1 - θ) * ε * (n : ℝ) := by positivity
  have hK : (ambientDimension ε θ n : ℝ) ≤
      (1 - θ) * ε * (n : ℝ) := by
    simpa [ambientDimension] using Nat.floor_le hxnonneg
  have hKsub : ((ambientDimension ε θ n - 1 : ℕ) : ℝ) ≤
      (1 - θ) * ε * (n : ℝ) := by
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hK
  have hcut :=
    higherJetDegreeBudgetAt_add_simplexWidthAt_cast_le (d := d) hθ.le
  norm_num only [Nat.cast_add] at hcut
  have hmain :
      (((ambientDimension ε θ n - 1) *
        (higherJetDegreeBudgetAt θ d +
          interpolationSimplexWidthAt θ d) : ℕ) : ℝ) <
        (multiplicityAt d : ℝ) * (ε * (n : ℝ)) := by
    push_cast
    calc
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ) *
          ((higherJetDegreeBudgetAt θ d : ℝ) +
            (interpolationSimplexWidthAt θ d : ℝ)) ≤
          ((ambientDimension ε θ n - 1 : ℕ) : ℝ) *
            ((1 + θ) * (multiplicityAt d : ℝ)) := by gcongr
      _ ≤ ((1 - θ) * ε * (n : ℝ)) *
            ((1 + θ) * (multiplicityAt d : ℝ)) := by gcongr
      _ = ((1 - θ) * (1 + θ)) *
            ((multiplicityAt d : ℝ) * (ε * (n : ℝ))) := by ring
      _ < 1 * ((multiplicityAt d : ℝ) * (ε * (n : ℝ))) := by
        exact mul_lt_mul_of_pos_right hfactor (by positivity)
      _ = (multiplicityAt d : ℝ) * (ε * (n : ℝ)) := by ring
  have hA : ε * (n : ℝ) ≤ (agreementThreshold ε n : ℝ) :=
    le_agreementThreshold ε n
  have hfinal :
      (((ambientDimension ε θ n - 1) *
        (higherJetDegreeBudgetAt θ d +
          interpolationSimplexWidthAt θ d) : ℕ) : ℝ) <
        ((multiplicityAt d * agreementThreshold ε n : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add] at hmain ⊢
    exact hmain.trans_le (mul_le_mul_of_nonneg_left hA hm.le)
  exact_mod_cast hfinal

/-- Weighted-budget estimate using the largest uniform simplex slack allowed
by the present higher-jet cutoff. -/
theorem optimizedSimplexFamilyAt_weightedBudget_lt
    {ε θ : ℝ} {d n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hd : 0 < d) (hn : 0 < n) :
    (ambientDimension ε θ n - 1) *
        (higherJetDegreeBudgetAt θ d +
          optimizedInterpolationSimplexWidthAt θ d) <
      multiplicityAt d * agreementThreshold ε n := by
  have hm : 0 < (multiplicityAt d : ℝ) := by
    exact_mod_cast multiplicityAt_pos hd
  have hxpos : 0 < (1 - θ) * ε * (n : ℝ) := by positivity
  have hxnonneg : 0 ≤ (1 - θ) * ε * (n : ℝ) := hxpos.le
  have hK : (ambientDimension ε θ n : ℝ) ≤
      (1 - θ) * ε * (n : ℝ) := by
    simpa [ambientDimension] using Nat.floor_le hxnonneg
  have hKsub : ((ambientDimension ε θ n - 1 : ℕ) : ℝ) <
      (1 - θ) * ε * (n : ℝ) := by
    by_cases hzero : ambientDimension ε θ n = 0
    · simp [hzero, hxpos]
    · have hpos : 0 < ambientDimension ε θ n := Nat.pos_of_ne_zero hzero
      have hsub : ambientDimension ε θ n - 1 <
          ambientDimension ε θ n := Nat.sub_lt hpos (by omega)
      exact (by exact_mod_cast hsub :
        ((ambientDimension ε θ n - 1 : ℕ) : ℝ) <
          (ambientDimension ε θ n : ℝ)).trans_le hK
  have hcut :=
    higherJetDegreeBudgetAt_add_optimizedSimplexWidthAt_cast_le
      hθ hθ₁ (d := d)
  norm_num only [Nat.cast_add] at hcut
  have hcutPos : 0 < (1 / (1 - θ)) * (multiplicityAt d : ℝ) := by
    positivity
  have hmain :
      (((ambientDimension ε θ n - 1) *
        (higherJetDegreeBudgetAt θ d +
          optimizedInterpolationSimplexWidthAt θ d) : ℕ) : ℝ) <
        (multiplicityAt d : ℝ) * (ε * (n : ℝ)) := by
    norm_num only [Nat.cast_mul, Nat.cast_add]
    calc
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ) *
          ((higherJetDegreeBudgetAt θ d : ℝ) +
            (optimizedInterpolationSimplexWidthAt θ d : ℝ)) ≤
        ((ambientDimension ε θ n - 1 : ℕ) : ℝ) *
          ((1 / (1 - θ)) * (multiplicityAt d : ℝ)) := by gcongr
      _ < ((1 - θ) * ε * (n : ℝ)) *
          ((1 / (1 - θ)) * (multiplicityAt d : ℝ)) :=
        mul_lt_mul_of_pos_right hKsub hcutPos
      _ = (multiplicityAt d : ℝ) * (ε * (n : ℝ)) := by
        field_simp [ne_of_gt (sub_pos.mpr hθ₁)]
  have hA : ε * (n : ℝ) ≤ (agreementThreshold ε n : ℝ) :=
    le_agreementThreshold ε n
  have hfinal :
      (((ambientDimension ε θ n - 1) *
        (higherJetDegreeBudgetAt θ d +
          optimizedInterpolationSimplexWidthAt θ d) : ℕ) : ℝ) <
        ((multiplicityAt d * agreementThreshold ε n : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add] at hmain ⊢
    exact hmain.trans_le (mul_le_mul_of_nonneg_left hA hm.le)
  exact_mod_cast hfinal

theorem boxFamilyAt_weightedBudget_lt
    {ε θ : ℝ} {d n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hd : 0 < d) (hn : 0 < n) :
    (ambientDimension ε θ n - 1) *
        (higherJetDegreeBudgetAt θ d +
          3 * interpolationBoxWidthAt θ d) <
      multiplicityAt d * agreementThreshold ε n := by
  have hfactor : (1 - θ) * (1 + θ) < 1 := by
    nlinarith [mul_pos hθ (sub_pos.mpr hθ₁)]
  have hm : 0 < (multiplicityAt d : ℝ) := by
    exact_mod_cast multiplicityAt_pos hd
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hxnonneg : 0 ≤ (1 - θ) * ε * (n : ℝ) := by positivity
  have hK : (ambientDimension ε θ n : ℝ) ≤
      (1 - θ) * ε * (n : ℝ) := by
    simpa [ambientDimension] using Nat.floor_le hxnonneg
  have hKsub : ((ambientDimension ε θ n - 1 : ℕ) : ℝ) ≤
      (1 - θ) * ε * (n : ℝ) := by
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hK
  have hcut :=
    higherJetDegreeBudgetAt_add_three_boxWidthAt_cast_le (d := d) hθ.le
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcut
  have hmain :
      (((ambientDimension ε θ n - 1) *
        (higherJetDegreeBudgetAt θ d +
          3 * interpolationBoxWidthAt θ d) : ℕ) : ℝ) <
        (multiplicityAt d : ℝ) * (ε * (n : ℝ)) := by
    push_cast
    calc
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ) *
          ((higherJetDegreeBudgetAt θ d : ℝ) +
            3 * (interpolationBoxWidthAt θ d : ℝ))
          ≤ ((ambientDimension ε θ n - 1 : ℕ) : ℝ) *
              ((1 + θ) * (multiplicityAt d : ℝ)) := by
                gcongr
      _ ≤ ((1 - θ) * ε * (n : ℝ)) *
              ((1 + θ) * (multiplicityAt d : ℝ)) := by
                gcongr
      _ = ((1 - θ) * (1 + θ)) *
              ((multiplicityAt d : ℝ) * (ε * (n : ℝ))) := by ring
      _ < 1 * ((multiplicityAt d : ℝ) * (ε * (n : ℝ))) := by
            exact mul_lt_mul_of_pos_right hfactor (by positivity)
      _ = (multiplicityAt d : ℝ) * (ε * (n : ℝ)) := by ring
  have hA : ε * (n : ℝ) ≤ (agreementThreshold ε n : ℝ) :=
    le_agreementThreshold ε n
  have hfinal :
      (((ambientDimension ε θ n - 1) *
        (higherJetDegreeBudgetAt θ d +
          3 * interpolationBoxWidthAt θ d) : ℕ) : ℝ) <
        ((multiplicityAt d * agreementThreshold ε n : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hmain ⊢
    exact hmain.trans_le (mul_le_mul_of_nonneg_left hA hm.le)
  exact_mod_cast hfinal

theorem le_interpolationDegreeBudgetAt_of_mul_denominator_lt
    {ε θ : ℝ} {d n t : ℕ} (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n)
    (ht : t * (ambientDimension ε θ n - 1) <
      multiplicityAt d * agreementThreshold ε n) :
    t ≤ interpolationDegreeBudgetAt d ε θ n := by
  by_contra hnot
  have hBt : interpolationDegreeBudgetAt d ε θ n < t :=
    Nat.lt_of_not_ge hnot
  have hden : 0 < ambientDimension ε θ n - 1 :=
    interpolationDenominatorAt_pos hd hdK
  have hmul :
      interpolationDegreeBudgetAt d ε θ n *
          (ambientDimension ε θ n - 1) <
        t * (ambientDimension ε θ n - 1) :=
    Nat.mul_lt_mul_of_pos_right hBt hden
  have hbudget :=
    multiplicityAt_mul_agreementThreshold_le_budget_mul_denominator hd hdK
  exact (not_lt_of_ge hbudget) (hmul.trans ht)

theorem interpolationBoxWidthAt_le_multiplicityAt
    {θ : ℝ} {d : ℕ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    interpolationBoxWidthAt θ d ≤ multiplicityAt d := by
  have hH := interpolationBoxWidthAt_cast_le (d := d) hθ.le
  have hm : 0 ≤ (multiplicityAt d : ℝ) := by positivity
  have hθtwelve : θ / 12 ≤ 1 := by linarith
  have hreal :
      (interpolationBoxWidthAt θ d : ℝ) ≤
        (multiplicityAt d : ℝ) := by
    calc
      (interpolationBoxWidthAt θ d : ℝ) ≤
          θ * (multiplicityAt d : ℝ) / 12 := hH
      _ = (θ / 12) * (multiplicityAt d : ℝ) := by ring
      _ ≤ 1 * (multiplicityAt d : ℝ) :=
        mul_le_mul_of_nonneg_right hθtwelve hm
      _ = (multiplicityAt d : ℝ) := one_mul _
  exact_mod_cast hreal

theorem freeGlobalDimensionSlacks
    {ε θ : ℝ} {d n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hd : 0 < d) (hn : 0 < n)
    (hdK : d < ambientDimension ε θ n) :
    interpolationBoxWidthAt θ d ≤ multiplicityAt d ∧
      higherJetDegreeBudgetAt θ d + 2 * interpolationBoxWidthAt θ d ≤
        interpolationDegreeBudgetAt d ε θ n ∧
      (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudgetAt θ d + 3 * interpolationBoxWidthAt θ d) ≤
        multiplicityAt d * agreementThreshold ε n := by
  have hweighted := boxFamilyAt_weightedBudget_lt hε hθ hθ₁ hd hn
  refine ⟨interpolationBoxWidthAt_le_multiplicityAt hθ hθ₁, ?_, hweighted.le⟩
  apply le_interpolationDegreeBudgetAt_of_mul_denominator_lt hd hdK
  calc
    (higherJetDegreeBudgetAt θ d + 2 * interpolationBoxWidthAt θ d) *
          (ambientDimension ε θ n - 1) =
        (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudgetAt θ d + 2 * interpolationBoxWidthAt θ d) := by
            ac_rfl
    _ ≤ (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudgetAt θ d + 3 * interpolationBoxWidthAt θ d) := by
            gcongr
            omega
    _ < multiplicityAt d * agreementThreshold ε n := hweighted

/-- Stronger slack package for the simplex count.  The three free exponent
directions share the single budget `3H`; this whole budget fits both the
ordinary-degree and weighted-degree constraints. -/
theorem freeGlobalDimensionSimplexSlacks
    {ε θ : ℝ} {d n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hd : 0 < d) (hn : 0 < n)
    (hdK : d < ambientDimension ε θ n) :
    3 * interpolationBoxWidthAt θ d ≤ multiplicityAt d ∧
      higherJetDegreeBudgetAt θ d +
          3 * interpolationBoxWidthAt θ d ≤
        interpolationDegreeBudgetAt d ε θ n ∧
      (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudgetAt θ d +
            3 * interpolationBoxWidthAt θ d) ≤
        multiplicityAt d * agreementThreshold ε n := by
  have hweighted := boxFamilyAt_weightedBudget_lt hε hθ hθ₁ hd hn
  have hHcast := interpolationBoxWidthAt_cast_le (d := d) hθ.le
  have hm : 0 ≤ (multiplicityAt d : ℝ) := by positivity
  have hthreeHReal :
      ((3 * interpolationBoxWidthAt θ d : ℕ) : ℝ) ≤
        (multiplicityAt d : ℝ) := by
    push_cast
    calc
      3 * (interpolationBoxWidthAt θ d : ℝ) ≤
          3 * (θ * (multiplicityAt d : ℝ) / 12) := by gcongr
      _ = (θ / 4) * (multiplicityAt d : ℝ) := by ring
      _ ≤ 1 * (multiplicityAt d : ℝ) := by
        gcongr
        linarith
      _ = (multiplicityAt d : ℝ) := one_mul _
  have hthreeH :
      3 * interpolationBoxWidthAt θ d ≤ multiplicityAt d := by
    exact_mod_cast hthreeHReal
  refine ⟨hthreeH, ?_, hweighted.le⟩
  apply le_interpolationDegreeBudgetAt_of_mul_denominator_lt hd hdK
  calc
    (higherJetDegreeBudgetAt θ d +
          3 * interpolationBoxWidthAt θ d) *
          (ambientDimension ε θ n - 1) =
        (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudgetAt θ d +
            3 * interpolationBoxWidthAt θ d) := by ac_rfl
    _ < multiplicityAt d * agreementThreshold ε n := hweighted

/-- Slack package using the largest directly rounded simplex width
`floor(θm/4)`, avoiding the loss from three separately rounded boxes. -/
theorem freeGlobalDimensionExactSimplexSlacks
    {ε θ : ℝ} {d n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hd : 0 < d) (hn : 0 < n)
    (hdK : d < ambientDimension ε θ n) :
    interpolationSimplexWidthAt θ d ≤ multiplicityAt d ∧
      higherJetDegreeBudgetAt θ d + interpolationSimplexWidthAt θ d ≤
        interpolationDegreeBudgetAt d ε θ n ∧
      (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudgetAt θ d +
            interpolationSimplexWidthAt θ d) ≤
        multiplicityAt d * agreementThreshold ε n := by
  have hweighted := simplexFamilyAt_weightedBudget_lt hε hθ hθ₁ hd hn
  have hJcast := interpolationSimplexWidthAt_cast_le (d := d) hθ.le
  have hm : 0 ≤ (multiplicityAt d : ℝ) := by positivity
  have hJReal :
      (interpolationSimplexWidthAt θ d : ℝ) ≤
        (multiplicityAt d : ℝ) := by
    calc
      (interpolationSimplexWidthAt θ d : ℝ) ≤
          θ * (multiplicityAt d : ℝ) / 4 := hJcast
      _ = (θ / 4) * (multiplicityAt d : ℝ) := by ring
      _ ≤ 1 * (multiplicityAt d : ℝ) := by
        gcongr
        linarith
      _ = (multiplicityAt d : ℝ) := one_mul _
  have hJ : interpolationSimplexWidthAt θ d ≤ multiplicityAt d := by
    exact_mod_cast hJReal
  refine ⟨hJ, ?_, hweighted.le⟩
  apply le_interpolationDegreeBudgetAt_of_mul_denominator_lt hd hdK
  calc
    (higherJetDegreeBudgetAt θ d + interpolationSimplexWidthAt θ d) *
          (ambientDimension ε θ n - 1) =
        (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudgetAt θ d +
            interpolationSimplexWidthAt θ d) := by ac_rfl
    _ < multiplicityAt d * agreementThreshold ε n := hweighted

/-- Slack package using the largest uniform simplex width permitted by the
current higher-jet cutoff and rate bound. -/
theorem freeGlobalDimensionOptimizedSimplexSlacks
    {ε θ : ℝ} {d n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hd : 0 < d) (hn : 0 < n)
    (hdK : d < ambientDimension ε θ n) :
    optimizedInterpolationSimplexWidthAt θ d ≤ multiplicityAt d ∧
      higherJetDegreeBudgetAt θ d +
          optimizedInterpolationSimplexWidthAt θ d ≤
        interpolationDegreeBudgetAt d ε θ n ∧
      (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudgetAt θ d +
            optimizedInterpolationSimplexWidthAt θ d) ≤
        multiplicityAt d * agreementThreshold ε n := by
  have hweighted :=
    optimizedSimplexFamilyAt_weightedBudget_lt hε hθ hθ₁ hd hn
  have hJcast :=
    optimizedInterpolationSimplexWidthAt_cast_le hθ hθ₁ (d := d)
  have hCoeff := optimizedSimplexSlackCoefficient_le_one θ
  have hJReal :
      (optimizedInterpolationSimplexWidthAt θ d : ℝ) ≤
        (multiplicityAt d : ℝ) := by
    calc
      (optimizedInterpolationSimplexWidthAt θ d : ℝ) ≤
          optimizedSimplexSlackCoefficient θ *
            (multiplicityAt d : ℝ) := hJcast
      _ ≤ 1 * (multiplicityAt d : ℝ) := by gcongr
      _ = (multiplicityAt d : ℝ) := one_mul _
  have hJ : optimizedInterpolationSimplexWidthAt θ d ≤
      multiplicityAt d := by exact_mod_cast hJReal
  refine ⟨hJ, ?_, hweighted.le⟩
  apply le_interpolationDegreeBudgetAt_of_mul_denominator_lt hd hdK
  calc
    (higherJetDegreeBudgetAt θ d +
          optimizedInterpolationSimplexWidthAt θ d) *
          (ambientDimension ε θ n - 1) =
        (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudgetAt θ d +
            optimizedInterpolationSimplexWidthAt θ d) := by ac_rfl
    _ < multiplicityAt d * agreementThreshold ε n := hweighted

theorem half_interpolationBoxWidthAtTarget_le_cast
    {θ : ℝ} {d : ℕ}
    (hlarge : 2 ≤ θ * (multiplicityAt d : ℝ) / 12) :
    θ * (multiplicityAt d : ℝ) / 24 ≤
      (interpolationBoxWidthAt θ d : ℝ) := by
  have hfloor := Nat.div_two_lt_floor
    (a := θ * (multiplicityAt d : ℝ) / 12) (by linarith)
  rw [interpolationBoxWidthAt]
  calc
    θ * (multiplicityAt d : ℝ) / 24 =
        (θ * (multiplicityAt d : ℝ) / 12) / 2 := by ring
    _ ≤ (⌊θ * (multiplicityAt d : ℝ) / 12⌋₊ : ℝ) := hfloor.le

/-- Near-lossless floor bound for the free-order interpolation width.  Once
the unrounded width is at least `d+1`, the relative floor loss is at most
`1/(d+1)` rather than the fixed factor two used by the original assembly. -/
theorem sharp_interpolationBoxWidthAtTarget_le_cast
    {θ : ℝ} {d : ℕ}
    (hlarge : (d : ℝ) + 1 ≤
      θ * (multiplicityAt d : ℝ) / 12) :
    (θ / 12) * ((d : ℝ) / (d + 1)) * (multiplicityAt d : ℝ) ≤
      (interpolationBoxWidthAt θ d : ℝ) := by
  let x := θ * (multiplicityAt d : ℝ) / 12
  have hd1 : 0 < (d : ℝ) + 1 := by positivity
  have hxnonneg : 0 ≤ x := by
    dsimp [x]
    linarith
  have hscaled : (d : ℝ) / (d + 1) * x ≤ x - 1 := by
    change (d : ℝ) + 1 ≤ x at hlarge
    rw [div_mul_eq_mul_div, div_le_iff₀ hd1]
    have hdiff : 0 ≤ x - ((d : ℝ) + 1) := sub_nonneg.mpr hlarge
    calc
      (d : ℝ) * x ≤ (d : ℝ) * x + (x - ((d : ℝ) + 1)) :=
        le_add_of_nonneg_right hdiff
      _ = (x - 1) * ((d : ℝ) + 1) := by ring
  have hfloor : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
  rw [interpolationBoxWidthAt]
  calc
    (θ / 12) * ((d : ℝ) / (d + 1)) *
          (multiplicityAt d : ℝ) =
        (d : ℝ) / (d + 1) * x := by
          dsimp [x]
          ring
    _ ≤ x - 1 := hscaled
    _ ≤ (⌊x⌋₊ : ℝ) := hfloor.le

/-- Near-lossless floor bound for the maximal simplex width. -/
theorem sharp_optimizedInterpolationSimplexWidthAtTarget_le_cast
    {θ : ℝ} {d : ℕ}
    (hlarge : (d : ℝ) + 1 ≤
      optimizedSimplexSlackCoefficient θ * (multiplicityAt d : ℝ)) :
    optimizedSimplexSlackCoefficient θ *
        ((d : ℝ) / (d + 1)) * (multiplicityAt d : ℝ) ≤
      (optimizedInterpolationSimplexWidthAt θ d : ℝ) := by
  let x := optimizedSimplexSlackCoefficient θ * (multiplicityAt d : ℝ)
  have hd1 : 0 < (d : ℝ) + 1 := by positivity
  have hxnonneg : 0 ≤ x := by
    dsimp [x]
    linarith
  have hscaled : (d : ℝ) / (d + 1) * x ≤ x - 1 := by
    change (d : ℝ) + 1 ≤ x at hlarge
    rw [div_mul_eq_mul_div, div_le_iff₀ hd1]
    have hdiff : 0 ≤ x - ((d : ℝ) + 1) := sub_nonneg.mpr hlarge
    calc
      (d : ℝ) * x ≤ (d : ℝ) * x + (x - ((d : ℝ) + 1)) :=
        le_add_of_nonneg_right hdiff
      _ = (x - 1) * ((d : ℝ) + 1) := by ring
  have hfloor : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
  rw [optimizedInterpolationSimplexWidthAt]
  calc
    optimizedSimplexSlackCoefficient θ *
          ((d : ℝ) / (d + 1)) * (multiplicityAt d : ℝ) =
        (d : ℝ) / (d + 1) * x := by
          dsimp [x]
          ring
    _ ≤ x - 1 := hscaled
    _ ≤ (⌊x⌋₊ : ℝ) := hfloor.le

end RSListDecoding
