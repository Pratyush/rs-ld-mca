import RSListDecoding.Lemmas.BoxWidthThreshold
import RSListDecoding.Lemmas.FreeParameters
import RSListDecoding.Lemmas.RankArithmetic
import RSListDecoding.Lemmas.ScaledShell

/-!
# The final rank comparison at arbitrary agreement

For fixed positive `ε` and `θ`, the sharp saving exponent
`θ / (2+θ)` is positive.  Consequently the final rank coefficient tends to
infinity with a freely chosen derivative order.  This is the step hidden by
the manuscript's special choice `d = ceil (ε^(-3/θ))`.
-/

noncomputable section

namespace RSListDecoding

open Filter

@[simp] theorem scaledShellWeight_eq_interpolationWeightBudgetAt
    (θ : ℝ) (d : ℕ) :
    scaledShellWeight θ d = interpolationWeightBudgetAt θ d := by
  simp [scaledShellWeight, interpolationWeightBudgetAt, multiplicityAt]

@[simp] theorem scaledShellDegree_eq_higherJetDegreeBudgetAt
    (θ : ℝ) (d : ℕ) :
    scaledShellDegree θ d = higherJetDegreeBudgetAt θ d := by
  simp [scaledShellDegree, higherJetDegreeBudgetAt, multiplicityAt]

/-- Exact rounding estimate.  Since `d < K`, the ratio `d/(d+2)` pays for
both the floor in `K` and the subsequent subtraction of one. -/
theorem order_ratio_mul_unroundedAmbient_le_ambientDimension_sub_one
    {ε θ : ℝ} {d n : ℕ} (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n) :
    ((d : ℝ) / (d + 2)) * ((1 - θ) * ε * (n : ℝ)) ≤
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ) := by
  have hdKle : d + 1 ≤ ambientDimension ε θ n := by omega
  have hK1 : 1 ≤ ambientDimension ε θ n := by omega
  have hround :
      (1 - θ) * ε * (n : ℝ) < (ambientDimension ε θ n : ℝ) + 1 := by
    simpa [ambientDimension] using
      (Nat.lt_floor_add_one ((1 - θ) * ε * (n : ℝ)))
  rw [Nat.cast_sub hK1]
  norm_num only [Nat.cast_one]
  have hdKle_real : (d : ℝ) + 1 ≤ ambientDimension ε θ n := by
    exact_mod_cast hdKle
  have hden : 0 < (d : ℝ) + 2 := by positivity
  calc
    (d : ℝ) / (d + 2) * ((1 - θ) * ε * (n : ℝ)) ≤
        (d : ℝ) / (d + 2) *
          ((ambientDimension ε θ n : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left hround.le
        (div_pos (by exact_mod_cast hd) hden).le
    _ ≤ (ambientDimension ε θ n : ℝ) - 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith

theorem order_ratio_mul_rate_le_ambientDimension_sub_one_div
    {ε θ : ℝ} {d n : ℕ} (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n) :
    ((d : ℝ) / (d + 2)) * ((1 - θ) * ε) ≤
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ) := by
  have hn : 0 < n := blockLength_pos_of_order_lt_ambientDimension hdK
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hn_real]
  have hrounded :=
    order_ratio_mul_unroundedAmbient_le_ambientDimension_sub_one hd hdK
  nlinarith [hrounded]

theorem rankSavingExponent_pos {θ : ℝ} (hθ : 0 < θ) :
    0 < rankSavingExponent θ := by
  unfold rankSavingExponent
  positivity

/-- Sharp power saved after the contact-envelope factor `1/d`. -/
def optimalRankSavingExponent (θ : ℝ) : ℝ := θ / (2 + θ)

theorem optimalRankSavingExponent_pos {θ : ℝ} (hθ : 0 < θ) :
    0 < optimalRankSavingExponent θ := by
  unfold optimalRankSavingExponent
  positivity

/-- The sharp shell exponent and sharp rank saving are complementary. -/
theorem optimalScaledShellExponent_add_optimalRankSavingExponent
    {θ : ℝ} (hθ : 0 < θ) :
    optimalScaledShellExponent θ + optimalRankSavingExponent θ = 1 := by
  unfold optimalScaledShellExponent optimalRankSavingExponent
  field_simp [ne_of_gt (by linarith : 0 < 2 + θ)]

/-- Explicit sharp saving extracted from the rounded shell factor. -/
theorem optimalScaledShellFactor_rankSaving_lower
    {θ : ℝ} (hθ : 0 < θ) {d : ℕ} (hd : 1 ≤ d) :
    (1 / (2 * Real.exp 3 + 1)) *
        (d : ℝ) ^ optimalRankSavingExponent θ ≤
      (d : ℝ) / (optimalScaledShellFactor θ d : ℝ) := by
  have hd0 : 0 < d := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd0
  have hfactorPos : 0 < (optimalScaledShellFactor θ d : ℝ) := by
    exact_mod_cast optimalScaledShellFactor_pos hd0
  have hconstantPos : 0 < 2 * Real.exp 3 + 1 := by positivity
  have hfactor := optimalScaledShellFactor_cast_le_const_mul_rpow hθ hd
  rw [le_div_iff₀ hfactorPos]
  calc
    (1 / (2 * Real.exp 3 + 1)) *
          (d : ℝ) ^ optimalRankSavingExponent θ *
          (optimalScaledShellFactor θ d : ℝ) ≤
        (1 / (2 * Real.exp 3 + 1)) *
          (d : ℝ) ^ optimalRankSavingExponent θ *
          ((2 * Real.exp 3 + 1) *
            (d : ℝ) ^ optimalScaledShellExponent θ) := by gcongr
    _ = (d : ℝ) ^
        (optimalScaledShellExponent θ + optimalRankSavingExponent θ) := by
      rw [Real.rpow_add hdR]
      field_simp
    _ = (d : ℝ) := by
      rw [optimalScaledShellExponent_add_optimalRankSavingExponent hθ,
        Real.rpow_one]

/-- At any fixed positive agreement and slack, all sufficiently large free
derivative orders satisfy the scalar rank comparison after replacing the
rounded ambient rate by its uniform lower bound. -/
theorem exists_freeOrderRankThreshold
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      1 < (θ ^ 3 / 110592) *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (d : ℝ) ^ rankSavingExponent θ := by
  have hcoefficient : 0 < (θ ^ 3 / 110592) * ((1 - θ) * ε / 2) := by
    positivity
  have hpower :
      Tendsto (fun d : ℕ => (d : ℝ) ^ rankSavingExponent θ)
        atTop atTop :=
    (tendsto_rpow_atTop (rankSavingExponent_pos hθ)).comp
      tendsto_natCast_atTop_atTop
  have hproduct :
      Tendsto
        (fun d : ℕ =>
          ((θ ^ 3 / 110592) * ((1 - θ) * ε / 2)) *
            (d : ℝ) ^ rankSavingExponent θ)
        atTop atTop :=
    hpower.const_mul_atTop hcoefficient
  obtain ⟨d₁, hd₁⟩ := eventually_atTop.mp
    (hproduct.eventually (eventually_gt_atTop (1 : ℝ)))
  refine ⟨max 2 d₁, ?_⟩
  intro d hdmax
  have hd2 : 2 ≤ d := (Nat.le_max_left 2 d₁).trans hdmax
  have hdbase : d₁ ≤ d := (Nat.le_max_right 2 d₁).trans hdmax
  have hhalf : (1 : ℝ) / 2 ≤ (d : ℝ) / (d + 2) := by
    have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have hden : 0 < (d : ℝ) + 2 := by positivity
    rw [le_div_iff₀ hden]
    linarith
  calc
    1 < (θ ^ 3 / 110592) * ((1 - θ) * ε / 2) *
        (d : ℝ) ^ rankSavingExponent θ := hd₁ d hdbase
    _ ≤ (θ ^ 3 / 110592) *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (d : ℝ) ^ rankSavingExponent θ := by
      gcongr
      nlinarith [mul_pos (sub_pos.mpr hθ₁) hε]

/-- Near-lossless rank threshold.  The floor and shell-ceiling losses are
kept as exact `d`-dependent ratios.  The displayed leading coefficient tends
to `θ³/3456`, thirty-two times the previous `θ³/110592`; eventual existence
already follows from the coarser comparison proved above. -/
theorem exists_sharpFreeOrderRankThreshold
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      1 < (θ ^ 3 / 3456) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        ((d : ℝ) / (scaledShellFactor θ d : ℝ)) := by
  obtain ⟨d₀, hd₀⟩ := exists_freeOrderRankThreshold hε hθ hθ₁
  refine ⟨max 2 d₀, ?_⟩
  intro d hdmax
  have hd2 : 2 ≤ d := (Nat.le_max_left 2 d₀).trans hdmax
  have hdbase : d₀ ≤ d := (Nat.le_max_right 2 d₀).trans hdmax
  have hd : 0 < d := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hshellPos : 0 < scaledShellFactor θ d := by
    rw [scaledShellFactor, Nat.ceil_pos]
    exact Real.rpow_pos_of_pos hdR _
  have hshellPosR : 0 < (scaledShellFactor θ d : ℝ) := by
    exact_mod_cast hshellPos
  have hhalfWidth :
      (1 : ℝ) / 2 ≤ (d : ℝ) / (d + 1) := by
    have hden : 0 < (d : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hden]
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcubeWidth :
      (1 : ℝ) / 8 ≤ ((d : ℝ) / (d + 1)) ^ 3 := by
    have hnonneg : 0 ≤ (1 : ℝ) / 2 := by positivity
    have hp := pow_le_pow_left₀ hnonneg hhalfWidth 3
    norm_num at hp ⊢
    exact hp
  have hshellUpper :
      (scaledShellFactor θ d : ℝ) ≤
        2 * (d : ℝ) ^ shellExponent θ := by
    exact scaledShellFactor_cast_le_two_rpow hθ hθ₁ (by omega)
  have hshellRatio :
      (1 / 2 : ℝ) * (d : ℝ) ^ rankSavingExponent θ ≤
        (d : ℝ) / (scaledShellFactor θ d : ℝ) := by
    rw [le_div_iff₀ hshellPosR]
    calc
      ((1 / 2 : ℝ) * (d : ℝ) ^ rankSavingExponent θ) *
          (scaledShellFactor θ d : ℝ) ≤
        ((1 / 2 : ℝ) * (d : ℝ) ^ rankSavingExponent θ) *
          (2 * (d : ℝ) ^ shellExponent θ) := by gcongr
      _ = (d : ℝ) ^
          (shellExponent θ + rankSavingExponent θ) := by
            rw [Real.rpow_add hdR]
            ring
      _ = (d : ℝ) := by
        rw [shellExponent_add_rankSavingExponent hθ, Real.rpow_one]
  have hcoarse := hd₀ d hdbase
  have hnonneg :
      0 ≤ (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (d : ℝ) ^ rankSavingExponent θ := by positivity
  calc
    1 < (θ ^ 3 / 110592) *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (d : ℝ) ^ rankSavingExponent θ := hcoarse
    _ ≤ (θ ^ 3 / 55296) *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (d : ℝ) ^ rankSavingExponent θ := by
      gcongr
      norm_num
    _ = (θ ^ 3 / 3456) * (1 / 8 : ℝ) *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        ((1 / 2 : ℝ) * (d : ℝ) ^ rankSavingExponent θ) := by ring
    _ ≤ (θ ^ 3 / 3456) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        ((d : ℝ) / (scaledShellFactor θ d : ℝ)) := by
      gcongr

/-- Fully sharp threshold, retaining the exact triangular contact count.
The leading coefficient tends to `θ³/1728`, sixty-four times the original
free-order coefficient. -/
theorem exists_triangleFreeOrderRankThreshold
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      1 < (θ ^ 3 / 1728) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := by
  obtain ⟨d₀, hd₀⟩ := exists_sharpFreeOrderRankThreshold hε hθ hθ₁
  refine ⟨max 2 d₀, ?_⟩
  intro d hdmax
  have hd2 : 2 ≤ d := (Nat.le_max_left 2 d₀).trans hdmax
  have hdbase : d₀ ≤ d := (Nat.le_max_right 2 d₀).trans hdmax
  have hd : 0 < d := by omega
  have hshell : 0 < (scaledShellFactor θ d : ℝ) := by
    exact_mod_cast scaledShellFactor_pos hd
  have hden : 0 < ((d : ℝ) ^ 2 + 1) := by positivity
  have hkernel :
      (d : ℝ) / (scaledShellFactor θ d : ℝ) ≤
        2 * (d : ℝ) ^ 3 /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ)) := by
    rw [div_le_iff₀ hshell]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    field_simp
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hcoarse := hd₀ d hdbase
  let common := (θ ^ 3 / 3456) * ((d : ℝ) / (d + 1)) ^ 3 *
    (((d : ℝ) / (d + 2)) * ((1 - θ) * ε))
  have hcommon : 0 ≤ common := by
    dsimp [common]
    positivity
  calc
    1 < common * ((d : ℝ) / (scaledShellFactor θ d : ℝ)) := by
      simpa [common, mul_assoc] using hcoarse
    _ ≤ common *
        (2 * (d : ℝ) ^ 3 /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) :=
      mul_le_mul_of_nonneg_left hkernel hcommon
    _ = (θ ^ 3 / 1728) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := by ring

/-- Threshold after exploiting the global slack simplex. -/
theorem exists_simplexFreeOrderRankThreshold
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      1 < (θ ^ 3 / 384) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := by
  obtain ⟨d₀, hd₀⟩ := exists_triangleFreeOrderRankThreshold hε hθ hθ₁
  refine ⟨d₀, ?_⟩
  intro d hd
  have htriangle := hd₀ d hd
  calc
    1 < (θ ^ 3 / 1728) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := htriangle
    _ ≤ (θ ^ 3 / 384) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := by
      gcongr
      norm_num

/-- Exact-floor simplex threshold.  Unlike the preceding smooth sufficient
condition, this is the concrete rank test consumed by the capstone. -/
theorem exists_exactSimplexFreeOrderRankThreshold
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      1 < (1 / 6) *
        ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := by
  obtain ⟨dRank, hRank⟩ :=
    exists_simplexFreeOrderRankThreshold hε hθ hθ₁
  obtain ⟨dBox, hBox⟩ :=
    exists_derivativeOrderThreshold_for_sharpBoxWidth hθ
  refine ⟨max dRank dBox, ?_⟩
  intro d hdmax
  have hdRank : dRank ≤ d := (Nat.le_max_left _ _).trans hdmax
  have hdBox : dBox ≤ d := (Nat.le_max_right _ _).trans hdmax
  have hsmooth := hRank d hdRank
  have hbox : (d : ℝ) + 1 ≤
      θ * (multiplicityAt d : ℝ) / 12 := by
    simpa [multiplicityAt] using hBox d hdBox
  have hwidth := sharp_interpolationBoxWidthAtTarget_le_cast hbox
  have hd : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    subst d
    norm_num [interpolationBoxWidthAt, multiplicityAt,
      scaledShellFactor] at hsmooth
  have hd3 : 0 < ((d ^ 3 : ℕ) : ℝ) := by positivity
  have hthreeBox : 3 * interpolationBoxWidthAt θ d ≤
      interpolationSimplexWidthAt θ d :=
    three_interpolationBoxWidthAt_le_simplexWidthAt hθ.le
  have hratio :
      3 * ((θ / 12) * ((d : ℝ) / (d + 1))) ≤
        (interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ) := by
    rw [le_div_iff₀ hd3]
    calc
      3 * ((θ / 12) * ((d : ℝ) / (d + 1))) * (d ^ 3 : ℕ) =
          3 * ((θ / 12) * ((d : ℝ) / (d + 1)) *
            (multiplicityAt d : ℝ)) := by simp [multiplicityAt]; ring
      _ ≤ 3 * (interpolationBoxWidthAt θ d : ℝ) := by gcongr
      _ ≤ (interpolationSimplexWidthAt θ d : ℝ) := by exact_mod_cast hthreeBox
  calc
    1 < (θ ^ 3 / 384) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := hsmooth
    _ = (1 / 6) *
        (3 * ((θ / 12) * ((d : ℝ) / (d + 1)))) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := by ring
    _ ≤ (1 / 6) *
        ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := by
      gcongr

/-- Exact-floor threshold with the sharp shell factor.  The old threshold
transfers because the new constant-times-`d^(2/(2+θ))` factor is eventually
no larger than the former slack-power ceiling. -/
theorem exists_optimalExactSimplexFreeOrderRankThreshold
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      1 < (1 / 6) *
        ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) *
            (optimalScaledShellFactor θ d : ℝ))) := by
  obtain ⟨dRank, hRank⟩ :=
    exists_exactSimplexFreeOrderRankThreshold hε hθ hθ₁
  obtain ⟨dFactor, hFactor⟩ := eventually_atTop.mp
    (eventually_optimalScaledShellFactor_le_scaledShellFactor hθ hθ₁)
  refine ⟨max dRank dFactor, ?_⟩
  intro d hdmax
  have hdRank : dRank ≤ d := (Nat.le_max_left _ _).trans hdmax
  have hdFactor : dFactor ≤ d := (Nat.le_max_right _ _).trans hdmax
  have hold := hRank d hdRank
  have hfactor := hFactor d hdFactor
  have hd : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    subst d
    norm_num [scaledShellFactor, optimalScaledShellFactor] at hold
  have holdPos : 0 < (scaledShellFactor θ d : ℝ) := by
    exact_mod_cast scaledShellFactor_pos hd
  have hnewPos : 0 < (optimalScaledShellFactor θ d : ℝ) := by
    exact_mod_cast optimalScaledShellFactor_pos hd
  have hkernel :
      ((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ)) ≤
        ((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) *
            (optimalScaledShellFactor θ d : ℝ)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hfactor)
      (by positivity)
  calc
    1 < (1 / 6) *
        ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := hold
    _ ≤ (1 / 6) *
        ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) *
            (optimalScaledShellFactor θ d : ℝ))) := by
      gcongr

/-- The same threshold supplies the exact comparison consumed by the
discrete dimension theorem, uniformly in the block length. -/
theorem freeOrder_rank_comparison
    {ε θ : ℝ} {d n : ℕ}
    (hθ : 0 < θ) (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n)
    (hlarge :
      1 < (θ ^ 3 / 110592) *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (d : ℝ) ^ rankSavingExponent θ) :
    1 < (θ ^ 3 / 110592) *
      (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (d : ℝ) ^ rankSavingExponent θ := by
  have hratio :=
    order_ratio_mul_rate_le_ambientDimension_sub_one_div hd hdK
  calc
    1 < (θ ^ 3 / 110592) *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (d : ℝ) ^ rankSavingExponent θ := hlarge
    _ ≤ (θ ^ 3 / 110592) *
        (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (d : ℝ) ^ rankSavingExponent θ := by
      gcongr

/-- Exact-shell analogue of `freeOrder_rank_comparison`. -/
theorem sharpFreeOrder_rank_comparison
    {ε θ : ℝ} {d n : ℕ}
    (hθ : 0 < θ) (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n)
    (hlarge :
      1 < (θ ^ 3 / 3456) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        ((d : ℝ) / (scaledShellFactor θ d : ℝ))) :
    1 < (θ ^ 3 / 3456) * ((d : ℝ) / (d + 1)) ^ 3 *
      (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      ((d : ℝ) / (scaledShellFactor θ d : ℝ)) := by
  have hratio :=
    order_ratio_mul_rate_le_ambientDimension_sub_one_div hd hdK
  calc
    1 < (θ ^ 3 / 3456) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        ((d : ℝ) / (scaledShellFactor θ d : ℝ)) := hlarge
    _ ≤ (θ ^ 3 / 3456) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
        ((d : ℝ) / (scaledShellFactor θ d : ℝ)) := by
      gcongr

/-- Exact-triangle analogue of `freeOrder_rank_comparison`. -/
theorem triangleFreeOrder_rank_comparison
    {ε θ : ℝ} {d n : ℕ}
    (hθ : 0 < θ) (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n)
    (hlarge :
      1 < (θ ^ 3 / 1728) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ)))) :
    1 < (θ ^ 3 / 1728) * ((d : ℝ) / (d + 1)) ^ 3 *
      (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (((d : ℝ) ^ 3) /
        (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := by
  have hratio :=
    order_ratio_mul_rate_le_ambientDimension_sub_one_div hd hdK
  calc
    1 < (θ ^ 3 / 1728) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := hlarge
    _ ≤ (θ ^ 3 / 1728) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := by
      gcongr

/-- Global-simplex analogue of `freeOrder_rank_comparison`. -/
theorem simplexFreeOrder_rank_comparison
    {ε θ : ℝ} {d n : ℕ}
    (hθ : 0 < θ) (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n)
    (hlarge :
      1 < (θ ^ 3 / 384) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ)))) :
    1 < (θ ^ 3 / 384) * ((d : ℝ) / (d + 1)) ^ 3 *
      (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (((d : ℝ) ^ 3) /
        (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := by
  have hratio :=
    order_ratio_mul_rate_le_ambientDimension_sub_one_div hd hdK
  calc
    1 < (θ ^ 3 / 384) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := hlarge
    _ ≤ (θ ^ 3 / 384) * ((d : ℝ) / (d + 1)) ^ 3 *
        (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) := by
      gcongr

/-- Exact-floor global-simplex rank comparison for an arbitrary positive
shell factor. -/
theorem exactSimplexFreeOrder_rank_comparison_of_factor
    {ε θ : ℝ} {d n R : ℕ}
    (hd : 0 < d) (hdK : d < ambientDimension ε θ n)
    (hlarge :
      1 < (1 / 6) *
        ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (R : ℝ)))) :
    1 < (1 / 6) *
      ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
      (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (((d : ℝ) ^ 3) /
        (((d : ℝ) ^ 2 + 1) * (R : ℝ))) := by
  have hratio :=
    order_ratio_mul_rate_le_ambientDimension_sub_one_div hd hdK
  calc
    1 < (1 / 6) *
        ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (R : ℝ))) := hlarge
    _ ≤ (1 / 6) *
        ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
      (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (((d : ℝ) ^ 3) /
        (((d : ℝ) ^ 2 + 1) * (R : ℝ))) := by
      gcongr

/-- Exact-floor global-simplex rank comparison for the original shell
factor. -/
theorem exactSimplexFreeOrder_rank_comparison
    {ε θ : ℝ} {d n : ℕ}
    (hd : 0 < d) (hdK : d < ambientDimension ε θ n)
    (hlarge :
      1 < (1 / 6) *
        ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ)))) :
    1 < (1 / 6) *
      ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
      (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (((d : ℝ) ^ 3) /
        (((d : ℝ) ^ 2 + 1) * (scaledShellFactor θ d : ℝ))) :=
  exactSimplexFreeOrder_rank_comparison_of_factor hd hdK hlarge

/-- Exact-floor global-simplex rank comparison for the sharp shell factor. -/
theorem optimalExactSimplexFreeOrder_rank_comparison
    {ε θ : ℝ} {d n : ℕ}
    (hd : 0 < d) (hdK : d < ambientDimension ε θ n)
    (hlarge :
      1 < (1 / 6) *
        ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
        (((d : ℝ) / (d + 2)) * ((1 - θ) * ε)) *
        (((d : ℝ) ^ 3) /
          (((d : ℝ) ^ 2 + 1) *
            (optimalScaledShellFactor θ d : ℝ)))) :
    1 < (1 / 6) *
      ((interpolationSimplexWidthAt θ d : ℝ) / (d ^ 3 : ℕ)) ^ 3 *
      (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (((d : ℝ) ^ 3) /
        (((d : ℝ) ^ 2 + 1) *
          (optimalScaledShellFactor θ d : ℝ))) :=
  exactSimplexFreeOrder_rank_comparison_of_factor hd hdK hlarge

end RSListDecoding
