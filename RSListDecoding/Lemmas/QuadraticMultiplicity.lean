import RSListDecoding.Lemmas.DimensionComparison
import RSListDecoding.Lemmas.RankArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Div

/-!
# Quadratic multiplicity parameter optimization

The paper fixes the interpolation multiplicity to `m = d^3`.  The discrete
rank and lattice arguments are in fact generic in `m`.  This file records the
real parameter calculation showing that `m = c d^2` is enough.

For weight coefficient `a` and quadratic constant `c`, the lattice sandwich
has shell exponent

`gamma(a,c) = (1 + 1/(2c))/a`.

The rate/root-counting budget requires `a < 1/(1-theta)`.  Consequently the
largest saving at fixed `c` is

`theta - (1-theta)/(2c)`.

In particular, every target saving `beta < theta` is feasible as soon as

`c > (1-theta)/(2(theta-beta))`.
-/

noncomputable section

namespace RSListDecoding

/-- Multiplicity schedule with a tunable quadratic leading constant. -/
def quadraticMultiplicityAt (c d : ℕ) : ℕ := c * d ^ 2

/-- Rounded anisotropic budget for the quadratic schedule.  The same real
coefficient is deliberately used by `quadraticShellDegree`; the retained
mass estimate does not require the older fixed coefficient gap. -/
noncomputable def quadraticShellWeight (a : ℝ) (c d : ℕ) : ℕ :=
  ⌊a * (d : ℝ) * (quadraticMultiplicityAt c d : ℝ) /
      (1 + Real.log (d : ℝ))⌋₊

/-- Rounded ordinary-degree cutoff with coefficient matching the weight
budget. -/
noncomputable def quadraticShellDegree (a : ℝ) (c d : ℕ) : ℕ :=
  ⌊a * (quadraticMultiplicityAt c d : ℝ)⌋₊

/-- Pointwise minimal finite shell factor for the quadratic parameters. -/
noncomputable def exactQuadraticShellFactor (a : ℝ) (c d : ℕ) : ℕ :=
  (scaledExponentCount d
      (quadraticShellWeight a c d + quadraticMultiplicityAt c d)) ⌈/⌉
    (goodScaledExponentCount d
      (quadraticShellWeight a c d) (quadraticShellDegree a c d))

/-- The exact quadratic factor satisfies the finite cardinality comparison
at every parameter value, independently of the asymptotic estimate. -/
theorem exactQuadraticShellFactor_spec (a : ℝ) (c d : ℕ) :
    scaledExponentCount d
        (quadraticShellWeight a c d + quadraticMultiplicityAt c d) ≤
      exactQuadraticShellFactor a c d *
        goodScaledExponentCount d
          (quadraticShellWeight a c d) (quadraticShellDegree a c d) := by
  have hden := goodScaledExponentCount_pos d
    (quadraticShellWeight a c d) (quadraticShellDegree a c d)
  have hreflexive :
      ((scaledExponentCount d
          (quadraticShellWeight a c d + quadraticMultiplicityAt c d)) ⌈/⌉
        (goodScaledExponentCount d
          (quadraticShellWeight a c d) (quadraticShellDegree a c d))) ≤
      ((scaledExponentCount d
          (quadraticShellWeight a c d + quadraticMultiplicityAt c d)) ⌈/⌉
        (goodScaledExponentCount d
          (quadraticShellWeight a c d) (quadraticShellDegree a c d))) := le_rfl
  simpa [exactQuadraticShellFactor, mul_comm] using
    (ceilDiv_le_iff_le_mul hden).mp hreflexive

theorem quadraticMultiplicityAt_pos {c d : ℕ}
    (hc : 0 < c) (hd : 0 < d) :
    0 < quadraticMultiplicityAt c d := by
  simp [quadraticMultiplicityAt, hc, hd]

/-- The contact-envelope quotient is linear in the derivative order under
the quadratic schedule. -/
theorem quadraticMultiplicityAt_div {c d : ℕ} (hd : 0 < d) :
    quadraticMultiplicityAt c d / d = c * d := by
  unfold quadraticMultiplicityAt
  calc
    c * d ^ 2 / d = (c * d) * d / d := by ring_nf
    _ = c * d := by
      simpa [Nat.mul_comm] using Nat.mul_div_right (c * d) hd

/-- Exponent paid by the shell ratio under the existing lattice sandwich. -/
def quadraticShellExponent (a c : ℝ) : ℝ :=
  (1 + 1 / (2 * c)) / a

/-- Complementary rank-saving exponent. -/
def quadraticRankSavingExponent (a c : ℝ) : ℝ :=
  1 - quadraticShellExponent a c

/-- Supremal saving allowed by the rate budget at fixed quadratic constant.
It is approached by taking the weight/degree coefficient `a` up to
`1/(1-theta)` while retaining a positive global-simplex width. -/
def quadraticSavingCeiling (θ c : ℝ) : ℝ :=
  θ - (1 - θ) / (2 * c)

theorem quadraticShellExponent_add_quadraticRankSavingExponent
    (a c : ℝ) :
    quadraticShellExponent a c + quadraticRankSavingExponent a c = 1 := by
  simp [quadraticRankSavingExponent]

/-- At the limiting rate coefficient, the saving is exactly the displayed
quadratic ceiling. -/
theorem quadratic_saving_at_rate_boundary
    {θ c : ℝ} (hc : c ≠ 0) :
    1 - (1 + 1 / (2 * c)) * (1 - θ) =
      quadraticSavingCeiling θ c := by
  unfold quadraticSavingCeiling
  field_simp [hc]
  ring

/-- The lower bound on `c` is precisely what makes the requested saving
strictly smaller than the quadratic ceiling. -/
theorem target_lt_quadraticSavingCeiling
    {θ β c : ℝ} (hc : 0 < c) (hβθ : β < θ)
    (hcLarge : (1 - θ) / (2 * (θ - β)) < c) :
    β < quadraticSavingCeiling θ c := by
  have hgap : 0 < θ - β := sub_pos.mpr hβθ
  have hden : 0 < 2 * c := by positivity
  have hmul := (div_lt_iff₀ (show 0 < 2 * (θ - β) by positivity)).mp hcLarge
  have hfrac : (1 - θ) / (2 * c) < θ - β := by
    rw [div_lt_iff₀ hden]
    nlinarith [hmul]
  unfold quadraticSavingCeiling
  linarith

/-- Feasible continuous parameters for every saving below the ceiling.

The returned `a` is the common coefficient used for the anisotropic weight
budget and ordinary-degree cutoff.  The positive `lambda ≤ 1` is the
remaining normalized width of the global three-dimensional slack simplex.
-/
theorem exists_quadratic_weight_and_simplex_coefficients
    {θ β c : ℝ} (_hθ : 0 < θ) (hθ₁ : θ < 1)
    (_hβ : 0 < β) (hβθ : β < θ) (hc : 0 < c)
    (hcLarge : (1 - θ) / (2 * (θ - β)) < c) :
    ∃ a lam : ℝ,
      0 < a ∧ 0 < lam ∧ lam ≤ 1 ∧
      a + lam < 1 / (1 - θ) ∧
      quadraticShellExponent a c < 1 - β := by
  let lower := (1 + 1 / (2 * c)) / (1 - β)
  let upper := 1 / (1 - θ)
  have hβ₁ : β < 1 := hβθ.trans hθ₁
  have hlowerPos : 0 < lower := by
    dsimp [lower]
    positivity
  have hupperPos : 0 < upper := by
    dsimp [upper]
    positivity
  have hceiling := target_lt_quadraticSavingCeiling hc hβθ hcLarge
  have hlowerUpper : lower < upper := by
    dsimp [lower, upper]
    unfold quadraticSavingCeiling at hceiling
    rw [div_lt_div_iff₀ (sub_pos.mpr hβ₁) (sub_pos.mpr hθ₁)]
    calc
      (1 + 1 / (2 * c)) * (1 - θ) =
          (1 - θ) + (1 - θ) / (2 * c) := by ring
      _ < 1 * (1 - β) := by simpa using (show
        (1 - θ) + (1 - θ) / (2 * c) < 1 - β by linarith)
  let a := (lower + upper) / 2
  let gap := upper - a
  let lam := min (gap / 2) (1 / 2)
  have haLower : lower < a := by
    dsimp [a]
    linarith
  have haUpper : a < upper := by
    dsimp [a]
    linarith
  have haPos : 0 < a := hlowerPos.trans haLower
  have hgapPos : 0 < gap := by
    dsimp [gap]
    linarith
  have hlamPos : 0 < lam := by
    dsimp [lam]
    exact lt_min (by positivity) (by norm_num)
  have hlamOne : lam ≤ 1 := by
    calc
      lam ≤ 1 / 2 := min_le_right _ _
      _ ≤ 1 := by norm_num
  have hlamGap : lam < gap := by
    calc
      lam ≤ gap / 2 := min_le_left _ _
      _ < gap := by linarith
  have hbudget : a + lam < upper := by
    dsimp [gap] at hlamGap
    linarith
  have hshell : quadraticShellExponent a c < 1 - β := by
    have hnumPos : 0 < 1 + 1 / (2 * c) := by positivity
    have hlowerEq : lower * (1 - β) = 1 + 1 / (2 * c) := by
      dsimp [lower]
      field_simp [ne_of_gt (sub_pos.mpr hβ₁)]
    unfold quadraticShellExponent
    rw [div_lt_iff₀ haPos]
    nlinarith
  exact ⟨a, lam, haPos, hlamPos, hlamOne, by simpa [upper] using hbudget,
    hshell⟩

/-- Exact continuous shell-cost identity behind the quadratic exponent.
Here `D` is represented by its asymptotic upper bound `d^2/2`. -/
theorem quadratic_shell_cost_identity
    {a c d L : ℝ} (ha : a ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (hL : L ≠ 0) :
    d * (c * d ^ 2 + d ^ 2 / 2) /
        (a * d * (c * d ^ 2) / L) =
      ((1 + 1 / (2 * c)) / a) * L := by
  field_simp [ha, hc, hd, hL]

/-- With matched weight and ordinary-degree coefficients, the exponent in
the bad-tuple estimate is exactly `L`; taking `L = 1 + log d` leaves the
constant good-mass fraction `1-e^{-1}` asymptotically. -/
theorem matched_bad_tuple_cost_identity
    {a c d L : ℝ} (ha : a ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (hL : L ≠ 0) :
    d * (a * (c * d ^ 2)) /
        (a * d * (c * d ^ 2) / L) = L := by
  field_simp [ha, hc, hd, hL]

/-- Real scalar comparison for an arbitrary multiplicity.  This is the
multiplicity-generic analogue of the `d^3` rank-arithmetic capstone.  The
factor

`m / (2 * (m / d + 1) * R)`

is exactly what remains after cancelling the common `m^3` scale between the
local contact envelope and the global slack simplex. -/
theorem contactEnvelope_scalar_lt_globalSimplex_general
    {widthCoefficient : ℝ} {d m K J R n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hR : 0 < R)
    (hwidthCoefficient : 0 ≤ widthCoefficient)
    (hJ : widthCoefficient * (m : ℝ) ≤ (J : ℝ))
    (hcompare :
      1 < (1 / 6) * widthCoefficient ^ 3 *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        ((m : ℝ) /
          (2 * ((m / d + 1 : ℕ) : ℝ) * (R : ℝ)))) :
    n * (m * (m / d + 1) * (2 * m) * R) <
      (K - 1) * (J + 2).choose 3 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hRR : 0 < (R : ℝ) := by exact_mod_cast hR
  have hquotR : 0 < ((m / d + 1 : ℕ) : ℝ) := by positivity
  have hmultPos :
      0 < (n : ℝ) * (m : ℝ) * ((m / d + 1 : ℕ) : ℝ) *
        (2 * (m : ℝ)) * (R : ℝ) := by positivity
  have hscaled := mul_lt_mul_of_pos_left hcompare hmultPos
  have hmiddle :
      (n : ℝ) * (m : ℝ) * ((m / d + 1 : ℕ) : ℝ) *
          (2 * (m : ℝ)) * (R : ℝ) <
        ((K - 1 : ℕ) : ℝ) *
          ((1 / 6) * (widthCoefficient * (m : ℝ)) ^ 3) := by
    calc
      (n : ℝ) * (m : ℝ) * ((m / d + 1 : ℕ) : ℝ) *
          (2 * (m : ℝ)) * (R : ℝ) =
          ((n : ℝ) * (m : ℝ) * ((m / d + 1 : ℕ) : ℝ) *
            (2 * (m : ℝ)) * (R : ℝ)) * 1 := by ring
      _ < ((n : ℝ) * (m : ℝ) * ((m / d + 1 : ℕ) : ℝ) *
            (2 * (m : ℝ)) * (R : ℝ)) *
          ((1 / 6) * widthCoefficient ^ 3 *
            (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
            ((m : ℝ) /
              (2 * ((m / d + 1 : ℕ) : ℝ) * (R : ℝ)))) := hscaled
      _ = ((K - 1 : ℕ) : ℝ) *
          ((1 / 6) * (widthCoefficient * (m : ℝ)) ^ 3) := by
        field_simp
  have hsimplex :
      (1 / 6 : ℝ) * (J : ℝ) ^ 3 ≤
        (((J + 2).choose 3 : ℕ) : ℝ) :=
    one_sixth_mul_cube_le_choose_add_two_cast J
  have hright :
      ((K - 1 : ℕ) : ℝ) *
          ((1 / 6) * (widthCoefficient * (m : ℝ)) ^ 3) ≤
        ((K - 1 : ℕ) : ℝ) *
          (((J + 2).choose 3 : ℕ) : ℝ) := by
    gcongr
    calc
      (1 / 6 : ℝ) * (widthCoefficient * (m : ℝ)) ^ 3 ≤
          (1 / 6 : ℝ) * (J : ℝ) ^ 3 := by
        gcongr
      _ ≤ (((J + 2).choose 3 : ℕ) : ℝ) := hsimplex
  have hfinal :
      ((n * (m * (m / d + 1) * (2 * m) * R) : ℕ) : ℝ) <
        (((K - 1) * (J + 2).choose 3 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc, mul_left_comm, mul_comm]
      using
      hmiddle.trans_le hright
  exact_mod_cast hfinal

/-- End-to-end finite rank comparison with arbitrary multiplicity.  It
combines the generic contact count, exact global slack simplex, shell bound,
and the scalar cancellation theorem above. -/
theorem total_contactEnvelope_finrank_lt_interpolationSpace_of_generalScalar
    {q d m A K B W C J R n : ℕ} [Fact (Nat.Prime q)]
    {widthCoefficient : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hn : 0 < n) (hR : 0 < R)
    (hJle : J ≤ m) (hdegree : C + J ≤ B)
    (hweighted : (K - 1) * (C + J) ≤ m * A)
    (hshell : scaledExponentCount d (W + m) ≤
      R * goodScaledExponentCount d W C)
    (hwidthCoefficient : 0 ≤ widthCoefficient)
    (hJlower : widthCoefficient * (m : ℝ) ≤ (J : ℝ))
    (hcompare :
      1 < (1 / 6) * widthCoefficient ^ 3 *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        ((m : ℝ) /
          (2 * ((m / d + 1 : ℕ) : ℝ) * (R : ℝ)))) :
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
      Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C) := by
  apply total_contactEnvelope_finrank_lt_interpolationSpace_simplex_general
    hd hJle hdegree hweighted hshell
  exact contactEnvelope_scalar_lt_globalSimplex_general
    hm hn hR hwidthCoefficient hJlower hcompare

end RSListDecoding
