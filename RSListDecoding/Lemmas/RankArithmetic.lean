import RSListDecoding.Lemmas.InterpolationArithmetic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Final scalar comparison for interpolation

This file isolates the final scalar comparisons.  Alongside the manuscript's
coarse rectangular estimates, it retains the exact shell ceiling, triangular
local contact region, near-exact floor ratio, and exact global slack-simplex
volume used by the optimized free-order capstone.
-/

noncomputable section

namespace RSListDecoding

/-- Exact real-volume estimate for a three-dimensional slack simplex. -/
theorem one_sixth_mul_cube_le_choose_add_two_cast (J : ℕ) :
    (1 / 6 : ℝ) * (J : ℝ) ^ 3 ≤
      (((J + 2).choose 3 : ℕ) : ℝ) := by
  have hdesc := Nat.descFactorial_eq_factorial_mul_choose (J + 2) 3
  have hsixNat :
      (J + 2) * (J + 1) * J = 6 * (J + 2).choose 3 := by
    calc
      (J + 2) * (J + 1) * J = J * ((J + 1) * (J + 2)) := by ring
      _ = 6 * (J + 2).choose 3 := by
        simpa [Nat.descFactorial, Nat.factorial] using hdesc
  have hsixReal :
      ((J + 2 : ℕ) : ℝ) * ((J + 1 : ℕ) : ℝ) * (J : ℝ) =
        6 * (((J + 2).choose 3 : ℕ) : ℝ) := by
    exact_mod_cast hsixNat
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hsixReal ⊢
  have hJ : 0 ≤ (J : ℝ) := by positivity
  nlinarith [sq_nonneg (J : ℝ)]

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

/-- Convert a real shell bound and an arbitrary positive rectangle-width
coefficient into the final strict natural dimension comparison.  Keeping the
coefficient symbolic lets different parameter assemblies avoid artificial
fixed-factor losses. -/
theorem contactEnvelope_scalar_lt_globalRectangle_with_width
    {θ widthCoefficient : ℝ} {d K H R n : ℕ}
    (hθ : 0 < θ) (hd : 0 < d) (hn : 0 < n)
    (hwidthCoefficient : 0 ≤ widthCoefficient)
    (hH : widthCoefficient * (d ^ 3 : ℕ) ≤ (H : ℝ))
    (hR : (R : ℝ) ≤ 2 * (d : ℝ) ^ shellExponent θ)
    (hcompare :
      1 < (widthCoefficient ^ 3 / 8) *
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
          (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3 := by
    calc
      8 * (n : ℝ) * (d : ℝ) ^ 8 *
          (d : ℝ) ^ shellExponent θ =
          (8 * (n : ℝ) * (d : ℝ) ^ 8 *
            (d : ℝ) ^ shellExponent θ) * 1 := by ring
      _ < (8 * (n : ℝ) * (d : ℝ) ^ 8 *
            (d : ℝ) ^ shellExponent θ) *
          ((widthCoefficient ^ 3 / 8) *
            (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
            (d : ℝ) ^ rankSavingExponent θ) := hscaled
      _ = ((K - 1 : ℕ) : ℝ) *
          (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3 := by
        calc
          8 * (n : ℝ) * (d : ℝ) ^ 8 *
                (d : ℝ) ^ shellExponent θ *
              ((widthCoefficient ^ 3 / 8) *
                (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
                (d : ℝ) ^ rankSavingExponent θ) =
              (8 * (n : ℝ) * (widthCoefficient ^ 3 / 8) *
                (((K - 1 : ℕ) : ℝ) / (n : ℝ)) * (d : ℝ) ^ 8) *
                ((d : ℝ) ^ shellExponent θ *
                  (d : ℝ) ^ rankSavingExponent θ) := by ring
          _ = (8 * (n : ℝ) * (widthCoefficient ^ 3 / 8) *
                (((K - 1 : ℕ) : ℝ) / (n : ℝ)) * (d : ℝ) ^ 8) *
                (d : ℝ) := by rw [hpowers]
          _ = ((K - 1 : ℕ) : ℝ) *
              (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3 := by
            field_simp
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
          (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3 ≤
        (((K - 1) * H ^ 3 : ℕ) : ℝ) := by
    push_cast
    gcongr
    simpa only [Nat.cast_pow] using hH
  have hfinal :
      ((n * (4 * d ^ 8 * R) : ℕ) : ℝ) <
        (((K - 1) * H ^ 3 : ℕ) : ℝ) :=
    hleft.trans_lt (hmiddle.trans_le hright)
  exact_mod_cast hfinal

/-- Exact version of the scalar comparison.  It keeps the natural shell
factor `R` in the denominator instead of replacing its ceiling by twice the
underlying real power.  This removes the asymptotic factor-two ceiling loss
from the free-order parameter assembly. -/
theorem contactEnvelope_scalar_lt_globalRectangle_exact
    {widthCoefficient : ℝ} {d K H R n : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hR : 0 < R)
    (hwidthCoefficient : 0 ≤ widthCoefficient)
    (hH : widthCoefficient * (d ^ 3 : ℕ) ≤ (H : ℝ))
    (hcompare :
      1 < (widthCoefficient ^ 3 / 2) *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        ((d : ℝ) / (R : ℝ))) :
    n * (2 * d ^ 8 * R) < (K - 1) * H ^ 3 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hRR : 0 < (R : ℝ) := by exact_mod_cast hR
  have hmultPos : 0 < 2 * (n : ℝ) * (d : ℝ) ^ 8 * (R : ℝ) := by
    positivity
  have hscaled := mul_lt_mul_of_pos_left hcompare hmultPos
  have hmiddle :
      2 * (n : ℝ) * (d : ℝ) ^ 8 * (R : ℝ) <
        ((K - 1 : ℕ) : ℝ) *
          (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3 := by
    calc
      2 * (n : ℝ) * (d : ℝ) ^ 8 * (R : ℝ) =
          (2 * (n : ℝ) * (d : ℝ) ^ 8 * (R : ℝ)) * 1 := by ring
      _ < (2 * (n : ℝ) * (d : ℝ) ^ 8 * (R : ℝ)) *
          ((widthCoefficient ^ 3 / 2) *
            (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
            ((d : ℝ) / (R : ℝ))) := hscaled
      _ = ((K - 1 : ℕ) : ℝ) *
          (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3 := by
        field_simp
  have hright :
      ((K - 1 : ℕ) : ℝ) *
          (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3 ≤
        ((K - 1 : ℕ) : ℝ) * (H : ℝ) ^ 3 := by
    gcongr
    simpa only [Nat.cast_pow] using hH
  have hfinal :
      ((n * (2 * d ^ 8 * R) : ℕ) : ℝ) <
        (((K - 1) * H ^ 3 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      hmiddle.trans_le hright
  exact_mod_cast hfinal

/-- Scalar comparison with the exact triangular contact factor
`d⁸+d⁶`. -/
theorem contactEnvelope_scalar_lt_globalRectangle_triangle
    {widthCoefficient : ℝ} {d K H R n : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hR : 0 < R)
    (hwidthCoefficient : 0 ≤ widthCoefficient)
    (hH : widthCoefficient * (d ^ 3 : ℕ) ≤ (H : ℝ))
    (hcompare :
      1 < widthCoefficient ^ 3 *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (R : ℝ)))) :
    n * ((d ^ 8 + d ^ 6) * R) < (K - 1) * H ^ 3 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hRR : 0 < (R : ℝ) := by exact_mod_cast hR
  have hden : 0 < ((d : ℝ) ^ 2 + 1) * (R : ℝ) := by positivity
  have hmultPos :
      0 < (n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ) := by
    positivity
  have hscaled := mul_lt_mul_of_pos_left hcompare hmultPos
  have hmiddle :
      (n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ) <
        ((K - 1 : ℕ) : ℝ) *
          (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3 := by
    calc
      (n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ) =
          ((n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ)) * 1 := by
            ring
      _ < ((n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ)) *
          (widthCoefficient ^ 3 *
            (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
            (((d : ℝ) ^ 3) /
              (((d : ℝ) ^ 2 + 1) * (R : ℝ)))) := hscaled
      _ = ((K - 1 : ℕ) : ℝ) *
          (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3 := by
        field_simp
  have hright :
      ((K - 1 : ℕ) : ℝ) *
          (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3 ≤
        ((K - 1 : ℕ) : ℝ) * (H : ℝ) ^ 3 := by
    gcongr
    simpa only [Nat.cast_pow] using hH
  have hfinal :
      ((n * ((d ^ 8 + d ^ 6) * R) : ℕ) : ℝ) <
        (((K - 1) * H ^ 3 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      hmiddle.trans_le hright
  exact_mod_cast hfinal

/-- Triangular-contact comparison with the integral factor-four lower bound
for the shared global slack simplex. -/
theorem contactEnvelope_scalar_lt_globalSimplex_triangle
    {widthCoefficient : ℝ} {d K H R n : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hR : 0 < R)
    (hwidthCoefficient : 0 ≤ widthCoefficient)
    (hH : widthCoefficient * (d ^ 3 : ℕ) ≤ (H : ℝ))
    (hcompare :
      1 < 4 * widthCoefficient ^ 3 *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (R : ℝ)))) :
    n * ((d ^ 8 + d ^ 6) * R) < (K - 1) * (4 * H ^ 3) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hRR : 0 < (R : ℝ) := by exact_mod_cast hR
  have hmultPos :
      0 < (n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ) := by
    positivity
  have hscaled := mul_lt_mul_of_pos_left hcompare hmultPos
  have hmiddle :
      (n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ) <
        ((K - 1 : ℕ) : ℝ) *
          (4 * (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3) := by
    calc
      (n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ) =
          ((n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ)) * 1 := by
            ring
      _ < ((n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ)) *
          (4 * widthCoefficient ^ 3 *
            (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
            (((d : ℝ) ^ 3) /
              (((d : ℝ) ^ 2 + 1) * (R : ℝ)))) := hscaled
      _ = ((K - 1 : ℕ) : ℝ) *
          (4 * (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3) := by
        field_simp
  have hright :
      ((K - 1 : ℕ) : ℝ) *
          (4 * (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3) ≤
        ((K - 1 : ℕ) : ℝ) * (4 * (H : ℝ) ^ 3) := by
    gcongr
    simpa only [Nat.cast_pow] using hH
  have hfinal :
      ((n * ((d ^ 8 + d ^ 6) * R) : ℕ) : ℝ) <
        (((K - 1) * (4 * H ^ 3) : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
      Nat.cast_ofNat]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      hmiddle.trans_le hright
  exact_mod_cast hfinal

/-- Exact simplex-volume version of the triangular-contact comparison. -/
theorem contactEnvelope_scalar_lt_globalSimplex_triangle_exact
    {widthCoefficient : ℝ} {d K J R n : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hR : 0 < R)
    (hwidthCoefficient : 0 ≤ widthCoefficient)
    (hJ : widthCoefficient * (d ^ 3 : ℕ) ≤ (J : ℝ))
    (hcompare :
      1 < (1 / 6) * widthCoefficient ^ 3 *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (R : ℝ)))) :
    n * ((d ^ 8 + d ^ 6) * R) <
      (K - 1) * (J + 2).choose 3 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hRR : 0 < (R : ℝ) := by exact_mod_cast hR
  have hmultPos :
      0 < (n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ) := by
    positivity
  have hscaled := mul_lt_mul_of_pos_left hcompare hmultPos
  have hmiddle :
      (n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ) <
        ((K - 1 : ℕ) : ℝ) *
          ((1 / 6) * (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3) := by
    calc
      (n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ) =
          ((n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ)) * 1 := by
            ring
      _ < ((n : ℝ) * ((d : ℝ) ^ 8 + (d : ℝ) ^ 6) * (R : ℝ)) *
          ((1 / 6) * widthCoefficient ^ 3 *
            (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
            (((d : ℝ) ^ 3) /
              (((d : ℝ) ^ 2 + 1) * (R : ℝ)))) := hscaled
      _ = ((K - 1 : ℕ) : ℝ) *
          ((1 / 6) * (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3) := by
        field_simp
  have hsimplex :
      (1 / 6 : ℝ) * (J : ℝ) ^ 3 ≤
        (((J + 2).choose 3 : ℕ) : ℝ) :=
    one_sixth_mul_cube_le_choose_add_two_cast J
  have hright :
      ((K - 1 : ℕ) : ℝ) *
          ((1 / 6) * (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3) ≤
        ((K - 1 : ℕ) : ℝ) *
          (((J + 2).choose 3 : ℕ) : ℝ) := by
    gcongr
    calc
      (1 / 6 : ℝ) * (widthCoefficient * ((d : ℝ) ^ 3)) ^ 3 ≤
          (1 / 6 : ℝ) * (J : ℝ) ^ 3 := by
        gcongr
        simpa only [Nat.cast_pow] using hJ
      _ ≤ (((J + 2).choose 3 : ℕ) : ℝ) := hsimplex
  have hfinal :
      ((n * ((d ^ 8 + d ^ 6) * R) : ℕ) : ℝ) <
        (((K - 1) * (J + 2).choose 3 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
      Nat.cast_ofNat]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      hmiddle.trans_le hright
  exact_mod_cast hfinal

/-- Original `/16`-width specialization, including the factor-two floor
rounding used by the manuscript capstones. -/
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
  apply contactEnvelope_scalar_lt_globalRectangle_with_width
    (widthCoefficient := θ / 32) hθ hd hn (by positivity)
  · simpa only [Nat.cast_pow, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using hH
  · exact hR
  · have heq : (θ / 32) ^ 3 / 8 = θ ^ 3 / 262144 := by ring
    rw [heq]
    exact hcompare

/-- Sharper `/12`-width specialization used by the free-order capstones. -/
theorem contactEnvelope_scalar_lt_globalRectangle_freeOrder
    {θ : ℝ} {d K H R n : ℕ}
    (hθ : 0 < θ) (hd : 0 < d) (hn : 0 < n)
    (hH : θ * (d ^ 3 : ℕ) / 24 ≤ (H : ℝ))
    (hR : (R : ℝ) ≤ 2 * (d : ℝ) ^ shellExponent θ)
    (hcompare :
      1 < (θ ^ 3 / 110592) *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (d : ℝ) ^ rankSavingExponent θ) :
    n * (4 * d ^ 8 * R) < (K - 1) * H ^ 3 := by
  apply contactEnvelope_scalar_lt_globalRectangle_with_width
    (widthCoefficient := θ / 24) hθ hd hn (by positivity)
  · simpa only [Nat.cast_pow, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using hH
  · exact hR
  · have heq : (θ / 24) ^ 3 / 8 = θ ^ 3 / 110592 := by ring
    rw [heq]
    exact hcompare

/-- Near-lossless free-order specialization.  Its coefficient approaches
`θ³ / 3456`, thirty-two times the previous `θ³ / 110592`: eight from the
true floor ratio, two from the exact shell ceiling, and two from triangular
contact counting. -/
theorem contactEnvelope_scalar_lt_globalRectangle_freeOrder_sharp
    {θ : ℝ} {d K H R n : ℕ}
    (hθ : 0 < θ) (hd : 0 < d) (hn : 0 < n) (hR : 0 < R)
    (hH :
      (θ / 12) * ((d : ℝ) / (d + 1)) * (d ^ 3 : ℕ) ≤ (H : ℝ))
    (hcompare :
      1 < (θ ^ 3 / 3456) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        ((d : ℝ) / (R : ℝ))) :
    n * (2 * d ^ 8 * R) < (K - 1) * H ^ 3 := by
  apply contactEnvelope_scalar_lt_globalRectangle_exact
    hd hn hR (show 0 ≤ (θ / 12) * ((d : ℝ) / (d + 1)) by positivity) hH
  have heq :
      (((θ / 12) * ((d : ℝ) / (d + 1))) ^ 3 / 2) =
        (θ ^ 3 / 3456) * ((d : ℝ) / (d + 1)) ^ 3 := by ring
  rw [heq]
  exact hcompare

/-- Exact triangular specialization.  Its coefficient tends to `θ³/1728`,
sixty-four times the coefficient in the preceding commit. -/
theorem contactEnvelope_scalar_lt_globalRectangle_freeOrder_triangle
    {θ : ℝ} {d K H R n : ℕ}
    (hθ : 0 < θ) (hd : 0 < d) (hn : 0 < n) (hR : 0 < R)
    (hH :
      (θ / 12) * ((d : ℝ) / (d + 1)) * (d ^ 3 : ℕ) ≤ (H : ℝ))
    (hcompare :
      1 < (θ ^ 3 / 1728) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (R : ℝ)))) :
    n * ((d ^ 8 + d ^ 6) * R) < (K - 1) * H ^ 3 := by
  apply contactEnvelope_scalar_lt_globalRectangle_triangle
    hd hn hR (show 0 ≤ (θ / 12) * ((d : ℝ) / (d + 1)) by positivity) hH
  have heq :
      ((θ / 12) * ((d : ℝ) / (d + 1))) ^ 3 =
        (θ ^ 3 / 1728) * ((d : ℝ) / (d + 1)) ^ 3 := by ring
  rw [heq]
  exact hcompare

/-- Free-order specialization using the global slack simplex.  The leading
coefficient tends to `θ³/432`, a factor `256` above the original free-order
assembly. -/
theorem contactEnvelope_scalar_lt_globalSimplex_freeOrder_triangle
    {θ : ℝ} {d K H R n : ℕ}
    (hθ : 0 < θ) (hd : 0 < d) (hn : 0 < n) (hR : 0 < R)
    (hH :
      (θ / 12) * ((d : ℝ) / (d + 1)) * (d ^ 3 : ℕ) ≤ (H : ℝ))
    (hcompare :
      1 < (θ ^ 3 / 432) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (R : ℝ)))) :
    n * ((d ^ 8 + d ^ 6) * R) < (K - 1) * (4 * H ^ 3) := by
  apply contactEnvelope_scalar_lt_globalSimplex_triangle
    hd hn hR (show 0 ≤ (θ / 12) * ((d : ℝ) / (d + 1)) by positivity) hH
  have heq :
      4 * ((θ / 12) * ((d : ℝ) / (d + 1))) ^ 3 =
        (θ ^ 3 / 432) * ((d : ℝ) / (d + 1)) ^ 3 := by ring
  rw [heq]
  exact hcompare

/-- Exact-volume free-order simplex specialization.  Its coefficient tends
to `θ³/384`, a factor `288` above the original free-order assembly. -/
theorem contactEnvelope_scalar_lt_globalSimplex_freeOrder_triangle_exact
    {θ : ℝ} {d K H R n : ℕ}
    (hθ : 0 < θ) (hd : 0 < d) (hn : 0 < n) (hR : 0 < R)
    (hH :
      (θ / 12) * ((d : ℝ) / (d + 1)) * (d ^ 3 : ℕ) ≤ (H : ℝ))
    (hcompare :
      1 < (θ ^ 3 / 384) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (R : ℝ)))) :
    n * ((d ^ 8 + d ^ 6) * R) <
      (K - 1) * (3 * H + 2).choose 3 := by
  apply contactEnvelope_scalar_lt_globalSimplex_triangle_exact
    (widthCoefficient := 3 * ((θ / 12) * ((d : ℝ) / (d + 1))))
    hd hn hR (by positivity) (by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      nlinarith)
  have heq :
      (1 / 6) * (3 * ((θ / 12) * ((d : ℝ) / (d + 1)))) ^ 3 =
        (θ ^ 3 / 384) * ((d : ℝ) / (d + 1)) ^ 3 := by ring
  rw [heq]
  exact hcompare

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
