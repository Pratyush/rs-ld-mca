import RSListDecoding.Lemmas.Parameters

/-!
# Arithmetic for the interpolation dimension comparison

This module isolates the rounded-parameter calculation at the end of the
interpolation argument.  In particular, it records why replacing the paper's
degree parameter by the ambient dimension

`K = floor ((1 - θ) * ε * n)`

still permits the lower bound on `(K - 1) / n`: the hypotheses imply `d ≥ 2`
and hence `K ≥ 3`, so the two units lost to the floor and to `K - 1` cost at
most a factor of two.
-/

namespace RSListDecoding

/-- For `0 < ε < 1` and `0 < θ`, the real number `ε ^ (-3 / θ)` is
strictly larger than one, so its natural ceiling is at least two. -/
theorem two_le_derivativeOrder {ε θ : ℝ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hθ : 0 < θ) :
    2 ≤ derivativeOrder ε θ := by
  have hexponent : -3 / θ < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hθ
  have hpow : 1 < ε ^ (-3 / θ) :=
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε hε₁ hexponent
  rw [derivativeOrder]
  have hpow' : ((1 : ℕ) : ℝ) < ε ^ (-3 / θ) := by
    simpa only [Nat.cast_one] using hpow
  exact Nat.succ_le_iff.mpr (Nat.lt_ceil.mpr hpow')

/-- The scoped hypothesis `d < K` already forces a nonempty block. -/
theorem blockLength_pos_of_derivativeOrder_lt_ambientDimension
    {ε θ : ℝ} {n : ℕ}
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  simp [ambientDimension] at hdK

/-- The two rounding losses in `K - 1`, one from the floor and one from the
subtraction, cost at most a factor of two in the scoped regime. -/
theorem half_unroundedAmbient_le_ambientDimension_sub_one
    {ε θ : ℝ} {n : ℕ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hθ : 0 < θ)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    ((1 - θ) * ε * (n : ℝ)) / 2 ≤
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ) := by
  have hd2 : 2 ≤ derivativeOrder ε θ := two_le_derivativeOrder hε hε₁ hθ
  have hK3 : 3 ≤ ambientDimension ε θ n := by omega
  have hK1 : 1 ≤ ambientDimension ε θ n := hK3.trans' (by omega)
  have hround :
      (1 - θ) * ε * (n : ℝ) < (ambientDimension ε θ n : ℝ) + 1 := by
    simpa [ambientDimension] using
      (Nat.lt_floor_add_one ((1 - θ) * ε * (n : ℝ)))
  rw [Nat.cast_sub hK1]
  have hK3_real : (3 : ℝ) ≤ ambientDimension ε θ n := by exact_mod_cast hK3
  linarith

/-- Division by the (automatically positive) block length gives the exact
ratio estimate used in the manuscript. -/
theorem half_rate_le_ambientDimension_sub_one_div
    {ε θ : ℝ} {n : ℕ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hθ : 0 < θ)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    (1 - θ) * ε / 2 ≤
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ) := by
  have hn : 0 < n := blockLength_pos_of_derivativeOrder_lt_ambientDimension hdK
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hn_real]
  have hhalf :=
    half_unroundedAmbient_le_ambientDimension_sub_one hε hε₁ hθ hdK
  nlinarith

/-- Raising the rounded derivative order to the positive comparison exponent
preserves the lower bound supplied by the ceiling. -/
theorem epsilon_rpow_le_derivativeOrder_rpow
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ε ^ (-6 / (5 + θ)) ≤
      (derivativeOrder ε θ : ℝ) ^ (2 * θ / (5 + θ)) := by
  have hdenom : 0 < 5 + θ := by linarith
  have hexponent : 0 ≤ 2 * θ / (5 + θ) := by positivity
  have hceil : ε ^ (-3 / θ) ≤ (derivativeOrder ε θ : ℝ) := by
    simpa [derivativeOrder] using Nat.le_ceil (ε ^ (-3 / θ))
  have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hε.le _) hceil hexponent
  calc
    ε ^ (-6 / (5 + θ)) =
        (ε ^ (-3 / θ)) ^ (2 * θ / (5 + θ)) := by
      rw [← Real.rpow_mul hε.le]
      congr 1
      field_simp
      ring
    _ ≤ (derivativeOrder ε θ : ℝ) ^ (2 * θ / (5 + θ)) := hmono

/-- The displayed small-`ε` condition is precisely strong enough to make
the unrounded coefficient comparison strictly larger than one. -/
theorem one_lt_tradeoff_coefficient
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hsmall :
      ε < (θ ^ 3 * (1 - θ) / 768) ^ ((5 + θ) / (1 - θ))) :
    1 < (θ ^ 3 * (1 - θ) / 768) *
      ε ^ (-((1 - θ) / (5 + θ))) := by
  have hbase : 0 < θ ^ 3 * (1 - θ) / 768 := by positivity
  have hr : 0 < (1 - θ) / (5 + θ) := by positivity
  have hpowered := Real.rpow_lt_rpow hε.le hsmall hr
  have hcancel :
      ((5 + θ) / (1 - θ)) * ((1 - θ) / (5 + θ)) = (1 : ℝ) := by
    field_simp [ne_of_gt (sub_pos.mpr hθ₁), ne_of_gt (by linarith : 0 < 5 + θ)]
  rw [← Real.rpow_mul hbase.le, hcancel, Real.rpow_one] at hpowered
  have hinverse_pos : 0 < ε ^ (-((1 - θ) / (5 + θ))) :=
    Real.rpow_pos_of_pos hε _
  have hmul := mul_lt_mul_of_pos_right hpowered hinverse_pos
  calc
    1 = ε ^ ((1 - θ) / (5 + θ)) *
        ε ^ (-((1 - θ) / (5 + θ))) := by
      rw [← Real.rpow_add hε, add_neg_cancel, Real.rpow_zero]
    _ < (θ ^ 3 * (1 - θ) / 768) *
        ε ^ (-((1 - θ) / (5 + θ))) := hmul

/-- The corrected ambient-`K` arithmetic needed to show that interpolation
dimension exceeds total local rank. -/
theorem one_lt_interpolation_rank_coefficient
    {ε θ : ℝ} {n : ℕ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hsmall :
      ε < (θ ^ 3 * (1 - θ) / 768) ^ ((5 + θ) / (1 - θ)))
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    1 < (θ ^ 3 / 384) *
      (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (derivativeOrder ε θ : ℝ) ^ (2 * θ / (5 + θ)) := by
  have hratio :=
    half_rate_le_ambientDimension_sub_one_div hε hε₁ hθ hdK
  have hpower := epsilon_rpow_le_derivativeOrder_rpow hε hθ
  have htrade := one_lt_tradeoff_coefficient hε hθ hθ₁ hsmall
  have hpowerProduct :
      ε ^ (-((1 - θ) / (5 + θ))) = ε * ε ^ (-6 / (5 + θ)) := by
    calc
      ε ^ (-((1 - θ) / (5 + θ))) =
          ε ^ ((1 : ℝ) + (-6 / (5 + θ))) := by
        congr 1
        field_simp [ne_of_gt (by linarith : 0 < 5 + θ)]
        ring
      _ = ε ^ (1 : ℝ) * ε ^ (-6 / (5 + θ)) :=
        Real.rpow_add hε _ _
      _ = ε * ε ^ (-6 / (5 + θ)) := by rw [Real.rpow_one]
  calc
    1 < (θ ^ 3 * (1 - θ) / 768) *
        ε ^ (-((1 - θ) / (5 + θ))) := htrade
    _ = (θ ^ 3 / 384) * ((1 - θ) * ε / 2) *
        ε ^ (-6 / (5 + θ)) := by
      rw [hpowerProduct]
      ring
    _ ≤ (θ ^ 3 / 384) *
        (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
        ε ^ (-6 / (5 + θ)) := by
      gcongr
    _ ≤ (θ ^ 3 / 384) *
        (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (derivativeOrder ε θ : ℝ) ^ (2 * θ / (5 + θ)) := by
      gcongr

/-! ## A rescaled comparison for repaired constant factors -/

/-- A version of the small-`ε` calculation with arbitrary positive leading
coefficient and target.  This lets later modules use deliberately coarse,
fully discrete dimension and rank estimates: their fixed constant loss is
absorbed by shrinking the existential `ε₀(θ)`. -/
theorem target_lt_interpolation_rank_coefficient
    {ε θ coefficient target : ℝ} {n : ℕ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hcoefficient : 0 < coefficient) (htarget : 0 < target)
    (hsmall :
      ε < (coefficient * (1 - θ) / (2 * target)) ^
        ((5 + θ) / (1 - θ)))
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    target < coefficient *
      (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (derivativeOrder ε θ : ℝ) ^ (2 * θ / (5 + θ)) := by
  have hbase : 0 < coefficient * (1 - θ) / (2 * target) := by
    positivity
  have hr : 0 < (1 - θ) / (5 + θ) := by positivity
  have hpowered := Real.rpow_lt_rpow hε.le hsmall hr
  have hcancel :
      ((5 + θ) / (1 - θ)) * ((1 - θ) / (5 + θ)) = (1 : ℝ) := by
    field_simp [ne_of_gt (sub_pos.mpr hθ₁), ne_of_gt (by linarith : 0 < 5 + θ)]
  rw [← Real.rpow_mul hbase.le, hcancel, Real.rpow_one] at hpowered
  have hinverse_pos : 0 < ε ^ (-((1 - θ) / (5 + θ))) :=
    Real.rpow_pos_of_pos hε _
  have hscaled := mul_lt_mul_of_pos_right hpowered
    (mul_pos htarget hinverse_pos)
  have htrade :
      target < (coefficient * (1 - θ) / 2) *
        ε ^ (-((1 - θ) / (5 + θ))) := by
    calc
      target = target *
          (ε ^ ((1 - θ) / (5 + θ)) *
            ε ^ (-((1 - θ) / (5 + θ)))) := by
        rw [← Real.rpow_add hε, add_neg_cancel, Real.rpow_zero, mul_one]
      _ = ε ^ ((1 - θ) / (5 + θ)) *
          (target * ε ^ (-((1 - θ) / (5 + θ)))) := by ring
      _ < (coefficient * (1 - θ) / (2 * target)) *
          (target * ε ^ (-((1 - θ) / (5 + θ)))) := hscaled
      _ = target *
          ((coefficient * (1 - θ) / (2 * target)) *
            ε ^ (-((1 - θ) / (5 + θ)))) := by ring
      _ = (coefficient * (1 - θ) / 2) *
          ε ^ (-((1 - θ) / (5 + θ))) := by field_simp
  have hratio :=
    half_rate_le_ambientDimension_sub_one_div hε hε₁ hθ hdK
  have hpower := epsilon_rpow_le_derivativeOrder_rpow hε hθ
  have hpowerProduct :
      ε ^ (-((1 - θ) / (5 + θ))) = ε * ε ^ (-6 / (5 + θ)) := by
    calc
      ε ^ (-((1 - θ) / (5 + θ))) =
          ε ^ ((1 : ℝ) + (-6 / (5 + θ))) := by
        congr 1
        field_simp [ne_of_gt (by linarith : 0 < 5 + θ)]
        ring
      _ = ε ^ (1 : ℝ) * ε ^ (-6 / (5 + θ)) :=
        Real.rpow_add hε _ _
      _ = ε * ε ^ (-6 / (5 + θ)) := by rw [Real.rpow_one]
  calc
    target < (coefficient * (1 - θ) / 2) *
        ε ^ (-((1 - θ) / (5 + θ))) := htrade
    _ = coefficient * ((1 - θ) * ε / 2) *
        ε ^ (-6 / (5 + θ)) := by rw [hpowerProduct]; ring
    _ ≤ coefficient *
        (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
        ε ^ (-6 / (5 + θ)) := by gcongr
    _ ≤ coefficient *
        (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (derivativeOrder ε θ : ℝ) ^ (2 * θ / (5 + θ)) := by gcongr

end RSListDecoding
