import RSListDecoding.Lemmas.BoxWidthThreshold
import RSListDecoding.Lemmas.FreeParameters
import RSListDecoding.Lemmas.RankArithmetic
import RSListDecoding.Lemmas.ScaledShell

/-!
# The final rank comparison at arbitrary agreement

For fixed positive `ε` and `θ`, the saving exponent
`2θ / (5+θ)` is positive.  Consequently the final rank coefficient tends to
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

end RSListDecoding
