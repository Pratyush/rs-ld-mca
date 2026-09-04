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

/-- A sharper eventual floor hypothesis for the free-order theorem.  The
linear loss `d/(d+1)` below pays exactly for the unit lost by the floor, so
we ask that the unrounded width be at least `d+1` rather than merely two.
The explicit threshold is still only linear in `1/θ`. -/
theorem exists_derivativeOrderThreshold_for_sharpBoxWidth
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      (d : ℝ) + 1 ≤ θ * ((d ^ 3 : ℕ) : ℝ) / 12 := by
  let D := max 2 ⌈24 / θ⌉₊
  refine ⟨D, ?_⟩
  intro d hd
  have hd2 : 2 ≤ d := (Nat.le_max_left 2 _).trans hd
  have hceilD : ⌈24 / θ⌉₊ ≤ d :=
    (Nat.le_max_right 2 _).trans hd
  have hceil : 24 / θ ≤ (⌈24 / θ⌉₊ : ℝ) := Nat.le_ceil _
  have hdreal : 24 / θ ≤ (d : ℝ) :=
    hceil.trans (by exact_mod_cast hceilD)
  have hlinear : 24 ≤ θ * (d : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hθ).mp hdreal
  have hdreal2 : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hquad : 12 * ((d : ℝ) + 1) ≤ 24 * (d : ℝ) ^ 2 := by
    nlinarith
  have hscaled : 12 * ((d : ℝ) + 1) ≤ θ * (d : ℝ) ^ 3 := by
    calc
      12 * ((d : ℝ) + 1) ≤ 24 * (d : ℝ) ^ 2 := hquad
      _ ≤ (θ * (d : ℝ)) * (d : ℝ) ^ 2 := by gcongr
      _ = θ * (d : ℝ) ^ 3 := by ring
  norm_num only [Nat.cast_pow]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12)]
  simpa [mul_comm] using hscaled

end RSListDecoding
