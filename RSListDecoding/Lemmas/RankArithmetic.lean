import RSListDecoding.Lemmas.InterpolationArithmetic

/-!
# Final scalar comparison for interpolation

The discrete counts lose two fixed factors: `4` in the direct contact-envelope
count and `2` when rounding the shell ratio.  Together with the factor `32³`
from the rectangular width, this leads to the coefficient
`θ³ / 262144`.  The scoped theorem has an existential `ε₀`, so this
fixed loss only asks us to shrink that threshold.
-/

noncomputable section

namespace RSListDecoding

/-- Exponent in the repaired shell ratio. -/
def shellExponent (θ : ℝ) : ℝ := (5 - θ) / (5 + θ)

/-- Positive exponent saved after the contact-envelope factor `1/d`. -/
def rankSavingExponent (θ : ℝ) : ℝ := 2 * θ / (5 + θ)

theorem shellExponent_add_rankSavingExponent {θ : ℝ}
    (hθ : 0 < θ) :
    shellExponent θ + rankSavingExponent θ = 1 := by
  unfold shellExponent rankSavingExponent
  field_simp [ne_of_gt (by linarith : 0 < 5 + θ)]
  ring

/-- Convert the real shell and width bounds into the final strict natural
dimension comparison. -/
theorem contactEnvelope_scalar_lt_globalRectangle
    {θ : ℝ} {d K H R n : ℕ}
    (hθ : 0 < θ) (hd : 0 < d) (hn : 0 < n)
    (hH : θ * (d ^ 3 : ℕ) / 32 ≤ (H : ℝ))
    (hR : (R : ℝ) ≤ 2 * (d : ℝ) ^ shellExponent θ)
    (hcompare :
      1 < (θ ^ 3 / 262144) *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (d : ℝ) ^ rankSavingExponent θ) :
    n * (4 * d ^ 8 * R) < (K - 1) * H ^ 3 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpowShell : 0 < (d : ℝ) ^ shellExponent θ :=
    Real.rpow_pos_of_pos hdR _
  have hmultPos :
      0 < 8 * (n : ℝ) * (d : ℝ) ^ 8 *
        (d : ℝ) ^ shellExponent θ := by positivity
  have hscaled := mul_lt_mul_of_pos_left hcompare hmultPos
  have hpowers :
      (d : ℝ) ^ shellExponent θ *
          (d : ℝ) ^ rankSavingExponent θ = (d : ℝ) := by
    rw [← Real.rpow_add hdR,
      shellExponent_add_rankSavingExponent hθ, Real.rpow_one]
  have hmiddle :
      8 * (n : ℝ) * (d : ℝ) ^ 8 *
          (d : ℝ) ^ shellExponent θ <
        ((K - 1 : ℕ) : ℝ) *
          (θ * ((d : ℝ) ^ 3) / 32) ^ 3 := by
    calc
      8 * (n : ℝ) * (d : ℝ) ^ 8 *
          (d : ℝ) ^ shellExponent θ =
          (8 * (n : ℝ) * (d : ℝ) ^ 8 *
            (d : ℝ) ^ shellExponent θ) * 1 := by ring
      _ < (8 * (n : ℝ) * (d : ℝ) ^ 8 *
            (d : ℝ) ^ shellExponent θ) *
          ((θ ^ 3 / 262144) *
            (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
            (d : ℝ) ^ rankSavingExponent θ) := hscaled
      _ = ((K - 1 : ℕ) : ℝ) *
          (θ * ((d : ℝ) ^ 3) / 32) ^ 3 := by
        calc
          8 * (n : ℝ) * (d : ℝ) ^ 8 *
                (d : ℝ) ^ shellExponent θ *
              ((θ ^ 3 / 262144) *
                (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
                (d : ℝ) ^ rankSavingExponent θ) =
              (8 * (n : ℝ) * (θ ^ 3 / 262144) *
                (((K - 1 : ℕ) : ℝ) / (n : ℝ)) * (d : ℝ) ^ 8) *
                ((d : ℝ) ^ shellExponent θ *
                  (d : ℝ) ^ rankSavingExponent θ) := by ring
          _ = (8 * (n : ℝ) * (θ ^ 3 / 262144) *
                (((K - 1 : ℕ) : ℝ) / (n : ℝ)) * (d : ℝ) ^ 8) *
                (d : ℝ) := by rw [hpowers]
          _ = ((K - 1 : ℕ) : ℝ) *
              (θ * ((d : ℝ) ^ 3) / 32) ^ 3 := by
            field_simp
            ring
  have hleft :
      ((n * (4 * d ^ 8 * R) : ℕ) : ℝ) ≤
        8 * (n : ℝ) * (d : ℝ) ^ 8 *
          (d : ℝ) ^ shellExponent θ := by
    push_cast
    calc
      (n : ℝ) * (4 * (d : ℝ) ^ 8 * (R : ℝ)) ≤
          (n : ℝ) *
            (4 * (d : ℝ) ^ 8 *
              (2 * (d : ℝ) ^ shellExponent θ)) := by gcongr
      _ = 8 * (n : ℝ) * (d : ℝ) ^ 8 *
          (d : ℝ) ^ shellExponent θ := by ring
  have hright :
      ((K - 1 : ℕ) : ℝ) *
          (θ * ((d : ℝ) ^ 3) / 32) ^ 3 ≤
        (((K - 1) * H ^ 3 : ℕ) : ℝ) := by
    push_cast
    gcongr
    simpa only [Nat.cast_pow] using hH
  have hfinal :
      ((n * (4 * d ^ 8 * R) : ℕ) : ℝ) <
        (((K - 1) * H ^ 3 : ℕ) : ℝ) :=
    hleft.trans_lt (hmiddle.trans_le hright)
  exact_mod_cast hfinal

/-- The additional small-`ε` bound sufficient for the repaired fixed
factors in the rank comparison. -/
def repairedRankEpsilonBound (θ : ℝ) : ℝ :=
  ((θ ^ 3 / 262144) * (1 - θ) / 2) ^ ((5 + θ) / (1 - θ))

theorem repairedRankEpsilonBound_pos {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) :
    0 < repairedRankEpsilonBound θ := by
  unfold repairedRankEpsilonBound
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The repaired small-`ε` condition yields precisely the real comparison
consumed above. -/
theorem one_lt_repaired_rank_coefficient
    {ε θ : ℝ} {n : ℕ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hsmall : ε < repairedRankEpsilonBound θ)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    1 < (θ ^ 3 / 262144) *
      (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (derivativeOrder ε θ : ℝ) ^ rankSavingExponent θ := by
  apply target_lt_interpolation_rank_coefficient hε hε₁ hθ hθ₁
      (coefficient := θ ^ 3 / 262144) (target := 1)
      (by positivity) (by norm_num) _ hdK
  simpa [repairedRankEpsilonBound] using hsmall

end RSListDecoding
