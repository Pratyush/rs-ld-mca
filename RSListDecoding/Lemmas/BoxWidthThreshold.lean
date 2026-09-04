import RSListDecoding.Defs.Parameters

/-!
# A large-derivative-order threshold for the interpolation box

The floor estimate for `interpolationBoxWidth` needs the unrounded box width
to be at least two.  This module isolates the elementary eventual estimate
that supplies that hypothesis once the derivative order is sufficiently
large.
-/

namespace RSListDecoding

/-- For fixed positive `θ`, the unrounded interpolation-box width is at
least two once `d` is sufficiently large.  The explicit threshold
`ceil (32 / θ)` is convenient for the final parameter assembly. -/
theorem exists_derivativeOrderThreshold_for_boxWidth
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      2 ≤ θ * ((d ^ 3 : ℕ) : ℝ) / 16 := by
  refine ⟨⌈32 / θ⌉₊, ?_⟩
  intro d hd
  have hthreshold_pos : 0 < ⌈32 / θ⌉₊ := by
    rw [Nat.ceil_pos]
    positivity
  have hd_pos : 0 < d := lt_of_lt_of_le hthreshold_pos hd
  have hd_one : (1 : ℝ) ≤ d := by
    exact_mod_cast (Nat.succ_le_iff.mpr hd_pos)
  have hceil : 32 / θ ≤ ((⌈32 / θ⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil (32 / θ)
  have hd_real : 32 / θ ≤ (d : ℝ) := by
    exact hceil.trans (by exact_mod_cast hd)
  have hlinear : 32 ≤ θ * (d : ℝ) := by
    have := (div_le_iff₀ hθ).mp hd_real
    nlinarith
  have hfactor :
      0 ≤ (d : ℝ) * ((d : ℝ) - 1) * ((d : ℝ) + 1) := by
    positivity
  have hcube : (d : ℝ) ≤ (d : ℝ) ^ 3 := by
    nlinarith [hfactor]
  have hscaled : 32 ≤ θ * (d : ℝ) ^ 3 :=
    hlinear.trans (mul_le_mul_of_nonneg_left hcube hθ.le)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
  norm_num
  exact hscaled

end RSListDecoding
