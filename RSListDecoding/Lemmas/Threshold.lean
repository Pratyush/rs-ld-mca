import RSListDecoding.Lemmas.Parameters

/-!
# Choosing the small-agreement threshold

The public statement intentionally quantifies an existential `ε₀(θ)`.  This
module supplies the reusable mechanism behind that quantifier: after shrinking
`ε₀` below the manuscript's displayed bound, the rounded derivative order
can be made larger than any prescribed natural threshold.  Later analytic and
integer estimates can therefore state their honest `d ≥ d₀(θ)` hypotheses.
-/

namespace RSListDecoding

/-- The displayed upper bound on `ε₀` in the scoped theorem. -/
noncomputable def manuscriptEpsilonBound (θ : ℝ) : ℝ :=
  (θ ^ 3 * (1 - θ) / 768) ^ ((5 + θ) / (1 - θ))

theorem manuscriptEpsilonBound_pos {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) :
    0 < manuscriptEpsilonBound θ := by
  unfold manuscriptEpsilonBound
  exact Real.rpow_pos_of_pos (by positivity) _

/-- An explicit positive cutoff forcing `derivativeOrder ε θ ≥ D`. -/
noncomputable def derivativeOrderCutoff (θ : ℝ) (D : ℕ) : ℝ :=
  ((D + 1 : ℕ) : ℝ) ^ (-θ / 3)

theorem derivativeOrderCutoff_pos {θ : ℝ} (D : ℕ) :
    0 < derivativeOrderCutoff θ D := by
  exact Real.rpow_pos_of_pos (by positivity) _

/-- Every positive `ε` below `derivativeOrderCutoff` has rounded derivative
depth at least `D`. -/
theorem le_derivativeOrder_of_lt_cutoff
    {ε θ : ℝ} {D : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ)
    (hcut : ε < derivativeOrderCutoff θ D) :
    D ≤ derivativeOrder ε θ := by
  have hexp : -3 / θ < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hθ
  have hanti := Real.rpow_lt_rpow_of_neg hε hcut hexp
  have hbase : 0 < (((D + 1 : ℕ) : ℝ)) := by positivity
  have hcollapse :
      (derivativeOrderCutoff θ D) ^ (-3 / θ) = (((D + 1 : ℕ) : ℝ)) := by
    rw [derivativeOrderCutoff, ← Real.rpow_mul hbase.le]
    have hθne : θ ≠ 0 := ne_of_gt hθ
    have hexponents : (-θ / 3) * (-3 / θ) = (1 : ℝ) := by
      field_simp
    rw [hexponents, Real.rpow_one]
  rw [hcollapse] at hanti
  rw [derivativeOrder]
  have hDreal : (D : ℝ) ≤ ε ^ (-3 / θ) := by
    exact (Nat.cast_le.mpr (Nat.le_add_right D 1)).trans hanti.le
  have hceil := hDreal.trans (Nat.le_ceil (ε ^ (-3 / θ)))
  exact_mod_cast hceil

/-- Simultaneously retain the manuscript bound and force an arbitrary lower
bound on `d`.  This is the standard constructor for the capstone's `ε₀`. -/
theorem exists_epsilonZero_with_derivativeOrder_threshold
    {θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1) (D : ℕ) :
    ∃ ε₀ : ℝ,
      0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ε₀ ≤ manuscriptEpsilonBound θ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → D ≤ derivativeOrder ε θ := by
  let ε₀ := min 1 (min (manuscriptEpsilonBound θ)
    (derivativeOrderCutoff θ D))
  refine ⟨ε₀, ?_, min_le_left _ _, ?_, ?_⟩
  · dsimp [ε₀]
    exact lt_min (by norm_num) <| lt_min
      (manuscriptEpsilonBound_pos hθ hθ₁)
      (derivativeOrderCutoff_pos D)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · intro ε hε hε₀
    apply le_derivativeOrder_of_lt_cutoff hε hθ
    exact hε₀.trans_le <| (min_le_right _ _).trans (min_le_right _ _)

/-- The same threshold constructor with one additional positive upper bound.
This is used to absorb fixed constant losses in the repaired discrete rank
and dimension estimates. -/
theorem exists_epsilonZero_below_with_derivativeOrder_threshold
    {θ bound : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hbound : 0 < bound) (D : ℕ) :
    ∃ ε₀ : ℝ,
      0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ε₀ ≤ manuscriptEpsilonBound θ ∧ ε₀ ≤ bound ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → D ≤ derivativeOrder ε θ := by
  let ε₀ := min bound <| min 1 <| min (manuscriptEpsilonBound θ)
    (derivativeOrderCutoff θ D)
  refine ⟨ε₀, ?_, ?_, ?_, min_le_left _ _, ?_⟩
  · dsimp [ε₀]
    exact lt_min hbound <| lt_min (by norm_num) <| lt_min
      (manuscriptEpsilonBound_pos hθ hθ₁)
      (derivativeOrderCutoff_pos D)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
  · intro ε hε hε₀
    apply le_derivativeOrder_of_lt_cutoff hε hθ
    exact hε₀.trans_le <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)

end RSListDecoding
