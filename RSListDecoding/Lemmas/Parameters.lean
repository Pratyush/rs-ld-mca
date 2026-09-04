import RSListDecoding.Defs.Parameters
import Mathlib.Tactic.Positivity

/-!
# Rounded-parameter facts

Elementary consequences of the parameter definitions used throughout the
combinatorial proof.  Keeping them here prevents later modules from repeatedly
unfolding real floors, ceilings, and powers.
-/

namespace RSListDecoding

/-- The integer threshold `A = ceil(εn)` is no stronger or weaker than the
real agreement inequality. -/
theorem agreementThreshold_le_iff (ε : ℝ) (n A : ℕ) :
    agreementThreshold ε n ≤ A ↔ ε * (n : ℝ) ≤ (A : ℝ) := by
  simp [agreementThreshold]

/-- The real target `εn` never exceeds its integer ceiling. -/
theorem le_agreementThreshold (ε : ℝ) (n : ℕ) :
    ε * (n : ℝ) ≤ agreementThreshold ε n := by
  simpa [agreementThreshold] using
    (Nat.le_ceil (ε * (n : ℝ)))

/-- A positive agreement fraction and nonempty block give a positive integer
agreement threshold. -/
theorem agreementThreshold_pos {ε : ℝ} {n : ℕ} (hε : 0 < ε) (hn : 0 < n) :
    0 < agreementThreshold ε n := by
  rw [agreementThreshold, Nat.ceil_pos]
  positivity

/-- The derivative depth is positive whenever `ε` is positive. -/
theorem derivativeOrder_pos {ε : ℝ} (θ : ℝ) (hε : 0 < ε) :
    0 < derivativeOrder ε θ := by
  rw [derivativeOrder, Nat.ceil_pos]
  exact Real.rpow_pos_of_pos hε _

/-- The multiplicity `m = d^3` is positive whenever `ε` is positive. -/
theorem multiplicity_pos {ε : ℝ} (θ : ℝ) (hε : 0 < ε) :
    0 < multiplicity ε θ := by
  exact pow_pos (derivativeOrder_pos θ hε) _

/-- The ambient interpolation dimension is strictly below the block length in
the scoped parameter regime. -/
theorem ambientDimension_lt_blockLength {ε θ : ℝ} {n : ℕ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hn : 0 < n) :
    ambientDimension ε θ n < n := by
  have hθfactor_nonneg : 0 ≤ 1 - θ := by linarith
  have hfactor_lt : (1 - θ) * ε < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_right (by linarith) hε.le hε₁
  have hnℝ : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [ambientDimension, Nat.floor_lt]
  · simpa using mul_lt_mul_of_pos_right hfactor_lt hnℝ
  · positivity

/-- Membership below the ambient integer dimension is equivalent to the
unrounded real rate inequality. -/
theorem le_ambientDimension_iff {ε θ : ℝ} {n k : ℕ}
    (hε : 0 ≤ ε) (hθ : θ ≤ 1) :
    k ≤ ambientDimension ε θ n ↔
      (k : ℝ) ≤ (1 - θ) * ε * (n : ℝ) := by
  rw [ambientDimension, Nat.le_floor_iff]
  positivity

/-- The scope hypothesis `d < K` makes the denominator `K-1` positive. -/
theorem interpolationDenominator_pos {ε θ : ℝ} {n : ℕ}
    (hε : 0 < ε)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    0 < ambientDimension ε θ n - 1 := by
  have hK : 1 < ambientDimension ε θ n :=
    lt_of_le_of_lt (derivativeOrder_pos θ hε) hdK
  omega

/-- The interpolation degree budget is positive in the scoped parameter
regime.  This supplies the positivity hypothesis in the external root-count
theorem rather than adding it to the public statement. -/
theorem interpolationDegreeBudget_pos {ε θ : ℝ} {n : ℕ}
    (hε : 0 < ε) (hn : 0 < n)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    0 < interpolationDegreeBudget ε θ n := by
  rw [interpolationDegreeBudget, Nat.ceil_pos]
  apply div_pos
  · exact_mod_cast Nat.mul_pos (multiplicity_pos θ hε)
      (agreementThreshold_pos hε hn)
  · exact_mod_cast interpolationDenominator_pos hε hdK

/-- Rounding `mA/(K-1)` upward gives the integral weighted-degree budget
inequality `mA ≤ B(K-1)`. -/
theorem multiplicity_mul_agreementThreshold_le_budget_mul_denominator
    {ε θ : ℝ} {n : ℕ} (hε : 0 < ε)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    multiplicity ε θ * agreementThreshold ε n ≤
      interpolationDegreeBudget ε θ n * (ambientDimension ε θ n - 1) := by
  have hdenNat : 0 < ambientDimension ε θ n - 1 :=
    interpolationDenominator_pos hε hdK
  have hdenReal : 0 < ((ambientDimension ε θ n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hdenNat
  have hceil :
      (((multiplicity ε θ * agreementThreshold ε n : ℕ) : ℝ) /
          ((ambientDimension ε θ n - 1 : ℕ) : ℝ)) ≤
        (interpolationDegreeBudget ε θ n : ℝ) := by
    simpa [interpolationDegreeBudget] using
      Nat.le_ceil
        (((multiplicity ε θ * agreementThreshold ε n : ℕ) : ℝ) /
          ((ambientDimension ε θ n - 1 : ℕ) : ℝ))
  have hreal :
      ((multiplicity ε θ * agreementThreshold ε n : ℕ) : ℝ) ≤
        (interpolationDegreeBudget ε θ n : ℝ) *
          ((ambientDimension ε θ n - 1 : ℕ) : ℝ) :=
    (div_le_iff₀ hdenReal).mp hceil
  exact_mod_cast hreal

/-- Since the positive denominator is at least one, the rounded degree budget
never exceeds the numerator `mA`. -/
theorem interpolationDegreeBudget_le_multiplicity_mul_agreementThreshold
    {ε θ : ℝ} {n : ℕ} (hε : 0 < ε)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n) :
    interpolationDegreeBudget ε θ n ≤
      multiplicity ε θ * agreementThreshold ε n := by
  rw [interpolationDegreeBudget, Nat.ceil_le]
  apply div_le_self
  · positivity
  · exact_mod_cast interpolationDenominator_pos hε hdK

/-! ## The two higher-jet cutoffs -/

/-- The floor defining the ordinary higher-jet cutoff is bounded by its real
argument. -/
theorem higherJetDegreeBudget_cast_le {ε θ : ℝ}
    (hθ : 0 ≤ θ) :
    (higherJetDegreeBudget ε θ : ℝ) ≤
      (1 + 3 * θ / 4) * (multiplicity ε θ : ℝ) := by
  rw [higherJetDegreeBudget]
  apply Nat.floor_le
  positivity

/-- The floor defining the rectangular interpolation width is bounded by its
real argument. -/
theorem interpolationBoxWidth_cast_le {ε θ : ℝ}
    (hθ : 0 ≤ θ) :
    (interpolationBoxWidth ε θ : ℝ) ≤
      θ * (multiplicity ε θ : ℝ) / 16 := by
  rw [interpolationBoxWidth]
  apply Nat.floor_le
  positivity

/-- The ordinary cutoff together with three copies of the rectangular width
fits below `(1+15θ/16)m`.  The three copies pay for the `X`, `Y₀`, and
`Y₁` choices in the discrete dimension injection. -/
theorem higherJetDegreeBudget_add_three_boxWidth_cast_le
    {ε θ : ℝ} (hθ : 0 ≤ θ) :
    ((higherJetDegreeBudget ε θ + 3 * interpolationBoxWidth ε θ : ℕ) : ℝ) ≤
      (1 + 15 * θ / 16) * (multiplicity ε θ : ℝ) := by
  push_cast
  have hC := higherJetDegreeBudget_cast_le (ε := ε) hθ
  have hH := interpolationBoxWidth_cast_le (ε := ε) hθ
  nlinarith

/-- The rectangular monomials used for the dimension lower bound satisfy the
strict global weighted-degree budget.  This is the rounded, ambient-`K`
version of the manuscript's slack estimate. -/
theorem boxFamily_weightedBudget_lt
    {ε θ : ℝ} {n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) (hn : 0 < n) :
    (ambientDimension ε θ n - 1) *
        (higherJetDegreeBudget ε θ + 3 * interpolationBoxWidth ε θ) <
      multiplicity ε θ * agreementThreshold ε n := by
  have hfactor : (1 - θ) * (1 + 15 * θ / 16) < 1 := by
    nlinarith [mul_pos hθ (sub_pos.mpr hθ₁)]
  have hm : 0 < (multiplicity ε θ : ℝ) := by
    exact_mod_cast multiplicity_pos θ hε
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hxnonneg : 0 ≤ (1 - θ) * ε * (n : ℝ) := by positivity
  have hK : (ambientDimension ε θ n : ℝ) ≤
      (1 - θ) * ε * (n : ℝ) := by
    simpa [ambientDimension] using Nat.floor_le hxnonneg
  have hKsub : ((ambientDimension ε θ n - 1 : ℕ) : ℝ) ≤
      (1 - θ) * ε * (n : ℝ) := by
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hK
  have hcut :=
    higherJetDegreeBudget_add_three_boxWidth_cast_le (ε := ε) hθ.le
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcut
  have hcut_nonneg :
      0 ≤ (1 + 15 * θ / 16) * (multiplicity ε θ : ℝ) := by
    positivity
  have hmain :
      (((ambientDimension ε θ n - 1) *
        (higherJetDegreeBudget ε θ + 3 * interpolationBoxWidth ε θ) : ℕ) : ℝ) <
        (multiplicity ε θ : ℝ) * (ε * (n : ℝ)) := by
    push_cast
    calc
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ) *
          ((higherJetDegreeBudget ε θ : ℝ) +
            3 * (interpolationBoxWidth ε θ : ℝ))
          ≤ ((ambientDimension ε θ n - 1 : ℕ) : ℝ) *
              ((1 + 15 * θ / 16) * (multiplicity ε θ : ℝ)) := by
                gcongr
      _ ≤ ((1 - θ) * ε * (n : ℝ)) *
              ((1 + 15 * θ / 16) * (multiplicity ε θ : ℝ)) := by
                gcongr
      _ = ((1 - θ) * (1 + 15 * θ / 16)) *
              ((multiplicity ε θ : ℝ) * (ε * (n : ℝ))) := by ring
      _ < 1 * ((multiplicity ε θ : ℝ) * (ε * (n : ℝ))) := by
            exact mul_lt_mul_of_pos_right hfactor (by positivity)
      _ = (multiplicity ε θ : ℝ) * (ε * (n : ℝ)) := by ring
  have hA : ε * (n : ℝ) ≤ (agreementThreshold ε n : ℝ) :=
    le_agreementThreshold ε n
  have hfinal :
      (((ambientDimension ε θ n - 1) *
        (higherJetDegreeBudget ε θ + 3 * interpolationBoxWidth ε θ) : ℕ) : ℝ) <
        ((multiplicity ε θ * agreementThreshold ε n : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hmain ⊢
    exact hmain.trans_le (mul_le_mul_of_nonneg_left hA hm.le)
  exact_mod_cast hfinal

/-- Any nonnegative jet-degree whose coarse weighted contribution is below
`mA` lies within the rounded individual degree budget `B`. -/
theorem le_interpolationDegreeBudget_of_mul_denominator_lt
    {ε θ : ℝ} {n t : ℕ} (hε : 0 < ε)
    (hdK : derivativeOrder ε θ < ambientDimension ε θ n)
    (ht : t * (ambientDimension ε θ n - 1) <
      multiplicity ε θ * agreementThreshold ε n) :
    t ≤ interpolationDegreeBudget ε θ n := by
  by_contra hnot
  have hBt : interpolationDegreeBudget ε θ n < t := Nat.lt_of_not_ge hnot
  have hden : 0 < ambientDimension ε θ n - 1 :=
    interpolationDenominator_pos hε hdK
  have hmul :
      interpolationDegreeBudget ε θ n * (ambientDimension ε θ n - 1) <
        t * (ambientDimension ε θ n - 1) :=
    Nat.mul_lt_mul_of_pos_right hBt hden
  have hbudget :=
    multiplicity_mul_agreementThreshold_le_budget_mul_denominator hε hdK
  exact (not_lt_of_ge hbudget) (hmul.trans ht)

/-- Every scoped message dimension is at most the block length. -/
theorem codeDimension_le_blockLength {ε θ : ℝ} {n k : ℕ}
    (hε : 0 < ε) (hε₁ : ε < 1) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hn : 0 < n)
    (hkK : k ≤ ambientDimension ε θ n) :
    k ≤ n :=
  hkK.trans <| (ambientDimension_lt_blockLength hε hε₁ hθ hθ₁ hn).le

/-- The exact geometric initial-jet count is bounded by replacing every level
with the largest one. -/
theorem rootCountGeometricFactor_le_top_mul
    {q e r : ℕ} (hq : 0 < q) :
    rootCountGeometricFactor q e r ≤
      (r + 1) * q ^ (e * (r + 1)) := by
  unfold rootCountGeometricFactor
  calc
    ∑ j ∈ Finset.range (r + 1), q ^ (e * (j + 1)) ≤
        ∑ _j ∈ Finset.range (r + 1), q ^ (e * (r + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.mem_range] at hj
      exact Nat.pow_le_pow_right hq
        (Nat.mul_le_mul_left e (by omega))
    _ = (r + 1) * q ^ (e * (r + 1)) := by simp

/-- A geometric sum with ratio at least two is strictly smaller than twice
its largest term. -/
theorem shiftedGeomSum_lt_two_mul_pow
    {x r : ℕ} (hx : 2 ≤ x) :
    (∑ j ∈ Finset.range (r + 1), x ^ (j + 1)) <
      2 * x ^ (r + 1) := by
  induction r with
  | zero => simp; omega
  | succ r ih =>
      rw [show r + 1 + 1 = (r + 1) + 1 by omega,
        Finset.sum_range_succ]
      have hscale : 2 * x ^ (r + 1) ≤ x ^ ((r + 1) + 1) := by
        calc
          2 * x ^ (r + 1) ≤ x * x ^ (r + 1) :=
            Nat.mul_le_mul_right _ hx
          _ = x ^ ((r + 1) + 1) := (pow_succ' x (r + 1)).symm
      omega

/-- Consequently the exact root-count factor has no linear-in-order
prefactor: it is less than twice its final term. -/
theorem rootCountGeometricFactor_lt_two_mul_top
    {q e r : ℕ} (hq : 2 ≤ q) (he : 0 < e) :
    rootCountGeometricFactor q e r <
      2 * q ^ (e * (r + 1)) := by
  have hqpos : 0 < q := by omega
  have hqpow : q ≤ q ^ e := by
    calc
      q = q ^ 1 := by simp
      _ ≤ q ^ e := Nat.pow_le_pow_right hqpos he
  have hratio : 2 ≤ q ^ e := hq.trans hqpow
  simpa only [rootCountGeometricFactor, pow_mul] using
    (shiftedGeomSum_lt_two_mul_pow (x := q ^ e) (r := r) hratio)

/-- The polynomial prefactor and exact quadratic-extension geometric sum fit
into the two spare powers of `q` in the public list bound. -/
theorem sharpRootCount_le_publicBound {d K n q B : ℕ}
    (hdK : d < K) (hKn : K < n) (hnq : n ≤ q) (hBq : B < q) :
    B * rootCountGeometricFactor q 2 d ≤ q ^ (2 * d + 4) := by
  have hdq : d + 1 ≤ q := (Nat.succ_le_iff.mpr hdK).trans (hKn.le.trans hnq)
  have hq : 0 < q := by omega
  calc
    B * rootCountGeometricFactor q 2 d
        ≤ B * ((d + 1) * q ^ (2 * (d + 1))) :=
      Nat.mul_le_mul_left B (rootCountGeometricFactor_le_top_mul hq)
    _ = B * (d + 1) * q ^ (2 * d + 2) := by
      rw [show 2 * (d + 1) = 2 * d + 2 by omega]
      simp [mul_assoc]
    _
        ≤ (q * q) * q ^ (2 * d + 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hBq.le hdq)
    _ = q ^ 2 * q ^ (2 * d + 2) := by rw [pow_two]
    _ = q ^ (2 + (2 * d + 2)) := (pow_add q 2 (2 * d + 2)).symm
    _ = q ^ (2 * d + 4) := by
      congr 1
      omega

/-- Absorb the two polynomial prefactors in the base-field root count. -/
theorem baseFieldRootCount_le_publicBound {d K n q B : ℕ}
    (hdK : d < K) (hKn : K < n) (hnq : n ≤ q) (hBq : B < q) :
    B * rootCountGeometricFactor q 1 d ≤ q ^ (d + 3) := by
  have hdq : d + 1 ≤ q := (Nat.succ_le_iff.mpr hdK).trans (hKn.le.trans hnq)
  have hq : 0 < q := by omega
  calc
    B * rootCountGeometricFactor q 1 d
        ≤ B * ((d + 1) * q ^ (1 * (d + 1))) :=
      Nat.mul_le_mul_left B (rootCountGeometricFactor_le_top_mul hq)
    _ = B * (d + 1) * q ^ (d + 1) := by simp [mul_assoc]
    _
        ≤ (q * q) * q ^ (d + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hBq.le hdq)
    _ = q ^ 2 * q ^ (d + 1) := by rw [pow_two]
    _ = q ^ (2 + (d + 1)) := (pow_add q 2 (d + 1)).symm
    _ = q ^ (d + 3) := by
      congr 1
      omega

end RSListDecoding
