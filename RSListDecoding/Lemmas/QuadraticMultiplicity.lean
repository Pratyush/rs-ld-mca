import RSListDecoding.Lemmas.DimensionComparison
import RSListDecoding.Lemmas.InterpolationKernel
import RSListDecoding.Lemmas.InterpolationVanishing
import RSListDecoding.Lemmas.Explainer
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

At fixed `beta`, the exact supremal normalized simplex width is

`min 1 (1/(1-theta) - (1+1/(2c))/(1-beta))`.

The quadratic schedule is divisible by `d`, so an exact triangular contact
count also removes the factor two in the generic local-rank estimate.  The
resulting supremal rank coefficient is the cube of the displayed width
divided by six.
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

/-- Supremal normalized width of the global slack simplex at target saving
`β`.  The second term is the exact rate budget left after taking the shell
coefficient down to its infimum; the outer minimum enforces `J ≤ m`. -/
def quadraticSimplexSlackCeiling (θ β c : ℝ) : ℝ :=
  min 1
    (1 / (1 - θ) - (1 + 1 / (2 * c)) / (1 - β))

/-- Supremal leading rank coefficient furnished by the exact global simplex
and exact triangular local contact count. -/
def quadraticRankCoefficient (θ β c : ℝ) : ℝ :=
  quadraticSimplexSlackCeiling θ β c ^ 3 / 6

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

/-- The saving hypothesis is equivalent to positive room between the shell
coefficient's infimum and the rate boundary. -/
theorem quadratic_shell_lower_lt_rate_boundary
    {θ β c : ℝ} (hθ₁ : θ < 1) (hβθ : β < θ) (hc : 0 < c)
    (hcLarge : (1 - θ) / (2 * (θ - β)) < c) :
    (1 + 1 / (2 * c)) / (1 - β) < 1 / (1 - θ) := by
  have hβ₁ : β < 1 := hβθ.trans hθ₁
  have hceiling := target_lt_quadraticSavingCeiling hc hβθ hcLarge
  unfold quadraticSavingCeiling at hceiling
  rw [div_lt_div_iff₀ (sub_pos.mpr hβ₁) (sub_pos.mpr hθ₁)]
  calc
    (1 + 1 / (2 * c)) * (1 - θ) =
        (1 - θ) + (1 - θ) / (2 * c) := by ring
    _ < 1 * (1 - β) := by linarith

theorem quadraticSimplexSlackCeiling_pos
    {θ β c : ℝ} (hθ₁ : θ < 1) (hβθ : β < θ) (hc : 0 < c)
    (hcLarge : (1 - θ) / (2 * (θ - β)) < c) :
    0 < quadraticSimplexSlackCeiling θ β c := by
  rw [quadraticSimplexSlackCeiling, lt_min_iff]
  exact ⟨zero_lt_one, sub_pos.mpr <|
    quadratic_shell_lower_lt_rate_boundary hθ₁ hβθ hc hcLarge⟩

theorem quadraticSimplexSlackCeiling_le_one (θ β c : ℝ) :
    quadraticSimplexSlackCeiling θ β c ≤ 1 := by
  exact min_le_left _ _

theorem quadraticRankCoefficient_pos
    {θ β c : ℝ} (hθ₁ : θ < 1) (hβθ : β < θ) (hc : 0 < c)
    (hcLarge : (1 - θ) / (2 * (θ - β)) < c) :
    0 < quadraticRankCoefficient θ β c := by
  unfold quadraticRankCoefficient
  positivity [quadraticSimplexSlackCeiling_pos hθ₁ hβθ hc hcLarge]

/-- Every simplex width strictly below the displayed ceiling is feasible.
This removes the two successive factor-two choices in the earlier midpoint
witness and exposes the optimal rank coefficient as a supremum. -/
theorem exists_quadratic_weight_coefficient_for_simplex_slack
    {θ β c lam : ℝ} (_hθ : 0 < θ) (hθ₁ : θ < 1)
    (_hβ : 0 < β) (hβθ : β < θ) (hc : 0 < c)
    (_hcLarge : (1 - θ) / (2 * (θ - β)) < c)
    (_hlam : 0 < lam)
    (hlamCeiling : lam < quadraticSimplexSlackCeiling θ β c) :
    ∃ a : ℝ,
      0 < a ∧ a + lam < 1 / (1 - θ) ∧
      quadraticShellExponent a c < 1 - β := by
  let lower := (1 + 1 / (2 * c)) / (1 - β)
  let upper := 1 / (1 - θ)
  have hβ₁ : β < 1 := hβθ.trans hθ₁
  have hlowerPos : 0 < lower := by
    dsimp [lower]
    positivity
  have hlamGap : lam < upper - lower := by
    have hraw := (lt_min_iff.mp (by
      simpa only [quadraticSimplexSlackCeiling] using hlamCeiling)).2
    simpa only [upper, lower] using hraw
  have hlowerUpperLam : lower < upper - lam := by linarith
  let a := (lower + (upper - lam)) / 2
  have haLower : lower < a := by
    dsimp [a]
    linarith
  have haUpper : a < upper - lam := by
    dsimp [a]
    linarith
  have haPos : 0 < a := hlowerPos.trans haLower
  have hbudget : a + lam < upper := by linarith
  have hshell : quadraticShellExponent a c < 1 - β := by
    have hnumPos : 0 < 1 + 1 / (2 * c) := by positivity
    have hlowerEq : lower * (1 - β) = 1 + 1 / (2 * c) := by
      dsimp [lower]
      field_simp [ne_of_gt (sub_pos.mpr hβ₁)]
    unfold quadraticShellExponent
    rw [div_lt_iff₀ haPos]
    nlinarith
  exact ⟨a, haPos, by simpa [upper] using hbudget, hshell⟩

/-- Explicit near-optimal specialization: for every relative loss
`0 < delta < 1`, one can retain the fraction `1-delta` of the supremal
simplex width. -/
theorem exists_quadratic_weight_coefficient_near_optimal
    {θ β c delta : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hβ : 0 < β) (hβθ : β < θ) (hc : 0 < c)
    (hcLarge : (1 - θ) / (2 * (θ - β)) < c)
    (hdelta : 0 < delta) (hdelta₁ : delta < 1) :
    ∃ a : ℝ,
      0 < a ∧
      a + (1 - delta) * quadraticSimplexSlackCeiling θ β c <
        1 / (1 - θ) ∧
      quadraticShellExponent a c < 1 - β := by
  have hceilingPos :=
    quadraticSimplexSlackCeiling_pos hθ₁ hβθ hc hcLarge
  have hlamPos :
      0 < (1 - delta) * quadraticSimplexSlackCeiling θ β c := by
    positivity
  have hlamCeiling :
      (1 - delta) * quadraticSimplexSlackCeiling θ β c <
        quadraticSimplexSlackCeiling θ β c := by
    nlinarith
  exact exists_quadratic_weight_coefficient_for_simplex_slack
    hθ hθ₁ hβ hβθ hc hcLarge hlamPos hlamCeiling

/-- Retaining a fraction `1-delta` of the optimal width retains exactly the
cube of that fraction of the optimal rank coefficient. -/
theorem near_optimal_quadratic_rank_coefficient (θ β c delta : ℝ) :
    ((1 - delta) * quadraticSimplexSlackCeiling θ β c) ^ 3 / 6 =
      (1 - delta) ^ 3 * quadraticRankCoefficient θ β c := by
  unfold quadraticRankCoefficient
  ring

/-- Conversely, every feasible width is bounded by the displayed ceiling.
Thus `quadraticRankCoefficient` is not merely an improved lower bound: it is
the supremal coefficient within this continuous parameter family. -/
theorem quadratic_simplex_slack_le_ceiling_of_feasible
    {θ β c a lam : ℝ} (hθ₁ : θ < 1) (hβθ : β < θ)
    (hc : 0 < c) (ha : 0 < a) (hlamOne : lam ≤ 1)
    (hbudget : a + lam < 1 / (1 - θ))
    (hshell : quadraticShellExponent a c < 1 - β) :
    lam ≤ quadraticSimplexSlackCeiling θ β c := by
  have hβ₁ : β < 1 := hβθ.trans hθ₁
  have hnumPos : 0 < 1 + 1 / (2 * c) := by positivity
  have haLower : (1 + 1 / (2 * c)) / (1 - β) < a := by
    rw [div_lt_iff₀ (sub_pos.mpr hβ₁)]
    unfold quadraticShellExponent at hshell
    rw [div_lt_iff₀ ha] at hshell
    simpa only [mul_comm] using hshell
  rw [quadraticSimplexSlackCeiling, le_min_iff]
  exact ⟨hlamOne, by linarith⟩

/-- Feasible continuous parameters for every saving below the ceiling.

The returned `a` is the common coefficient used for the anisotropic weight
budget and ordinary-degree cutoff.  The positive `lambda ≤ 1` is the
remaining normalized width of the global three-dimensional slack simplex.
-/
theorem exists_quadratic_weight_and_simplex_coefficients
    {θ β c : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hβ : 0 < β) (hβθ : β < θ) (hc : 0 < c)
    (hcLarge : (1 - θ) / (2 * (θ - β)) < c) :
    ∃ a lam : ℝ,
      0 < a ∧ 0 < lam ∧ lam ≤ 1 ∧
      a + lam < 1 / (1 - θ) ∧
      quadraticShellExponent a c < 1 - β := by
  let lam := quadraticSimplexSlackCeiling θ β c / 2
  have hceilingPos :=
    quadraticSimplexSlackCeiling_pos hθ₁ hβθ hc hcLarge
  have hlamPos : 0 < lam := by
    dsimp [lam]
    positivity
  have hlamCeiling : lam < quadraticSimplexSlackCeiling θ β c := by
    dsimp [lam]
    linarith
  obtain ⟨a, haPos, hbudget, hshell⟩ :=
    exists_quadratic_weight_coefficient_for_simplex_slack
      hθ hθ₁ hβ hβθ hc hcLarge hlamPos hlamCeiling
  have hlamOne : lam ≤ 1 := by
    calc
      lam ≤ quadraticSimplexSlackCeiling θ β c := hlamCeiling.le
      _ ≤ 1 := quadraticSimplexSlackCeiling_le_one θ β c
  exact ⟨a, lam, haPos, hlamPos, hlamOne, hbudget, hshell⟩

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
the bad-tuple estimate is exactly `L`; taking `L = 1 + log d` leaves a fixed
good-mass fraction `1-e^{-1}` in the limit. -/
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

/-- Sharp scalar comparison when the derivative depth divides the
multiplicity.  The exact triangular contact geometry removes the factor two
from `contactEnvelope_scalar_lt_globalSimplex_general`. -/
theorem contactEnvelope_scalar_lt_globalSimplex_divisible
    {widthCoefficient : ℝ} {d m K J R n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hR : 0 < R)
    (hwidthCoefficient : 0 ≤ widthCoefficient)
    (hJ : widthCoefficient * (m : ℝ) ≤ (J : ℝ))
    (hcompare :
      1 < (1 / 6) * widthCoefficient ^ 3 *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        ((m : ℝ) /
          (((m / d + 1 : ℕ) : ℝ) * (R : ℝ)))) :
    n * (m * (m / d + 1) * m * R) <
      (K - 1) * (J + 2).choose 3 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hRR : 0 < (R : ℝ) := by exact_mod_cast hR
  have hquotR : 0 < ((m / d + 1 : ℕ) : ℝ) := by positivity
  have hmultPos :
      0 < (n : ℝ) * (m : ℝ) * ((m / d + 1 : ℕ) : ℝ) *
        (m : ℝ) * (R : ℝ) := by positivity
  have hscaled := mul_lt_mul_of_pos_left hcompare hmultPos
  have hmiddle :
      (n : ℝ) * (m : ℝ) * ((m / d + 1 : ℕ) : ℝ) *
          (m : ℝ) * (R : ℝ) <
        ((K - 1 : ℕ) : ℝ) *
          ((1 / 6) * (widthCoefficient * (m : ℝ)) ^ 3) := by
    calc
      (n : ℝ) * (m : ℝ) * ((m / d + 1 : ℕ) : ℝ) *
          (m : ℝ) * (R : ℝ) =
          ((n : ℝ) * (m : ℝ) * ((m / d + 1 : ℕ) : ℝ) *
            (m : ℝ) * (R : ℝ)) * 1 := by ring
      _ < ((n : ℝ) * (m : ℝ) * ((m / d + 1 : ℕ) : ℝ) *
            (m : ℝ) * (R : ℝ)) *
          ((1 / 6) * widthCoefficient ^ 3 *
            (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
            ((m : ℝ) /
              (((m / d + 1 : ℕ) : ℝ) * (R : ℝ)))) := hscaled
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
      ((n * (m * (m / d + 1) * m * R) : ℕ) : ℝ) <
        (((K - 1) * (J + 2).choose 3 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc, mul_left_comm, mul_comm]
      using hmiddle.trans_le hright
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

/-- End-to-end finite rank comparison with the optimized coefficient for a
multiplicity divisible by the derivative depth. -/
theorem total_contactEnvelope_finrank_lt_interpolationSpace_of_divisibleScalar
    {q d m A K B W C J R n : ℕ} [Fact (Nat.Prime q)]
    {widthCoefficient : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hn : 0 < n) (hR : 0 < R)
    (hdm : d ∣ m)
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
          (((m / d + 1 : ℕ) : ℝ) * (R : ℝ)))) :
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
      Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C) := by
  apply total_contactEnvelope_finrank_lt_interpolationSpace_simplex_divisible
    hd hdm hJle hdegree hweighted hshell
  exact contactEnvelope_scalar_lt_globalSimplex_divisible
    hm hn hR hwidthCoefficient hJlower hcompare

/-- The quadratic multiplicity is automatically divisible by the derivative
depth, so the optimized triangular coefficient always applies. -/
theorem derivativeDepth_dvd_quadraticMultiplicityAt (c d : ℕ) :
    d ∣ quadraticMultiplicityAt c d := by
  refine ⟨c * d, ?_⟩
  simp [quadraticMultiplicityAt]
  ring

/-- Exact finite quotient appearing in the optimized quadratic rank
comparison.  Its ratio to `d` tends to one for every fixed positive `c`; the
older rectangular comparison had limiting ratio `d/2`. -/
theorem quadratic_rank_quotient_eq
    {c d R : ℕ} (hd : 0 < d) :
    (quadraticMultiplicityAt c d : ℝ) /
        (((quadraticMultiplicityAt c d / d + 1 : ℕ) : ℝ) * (R : ℝ)) =
      ((c * d ^ 2 : ℕ) : ℝ) /
        (((c * d + 1 : ℕ) : ℝ) * (R : ℝ)) := by
  rw [quadraticMultiplicityAt_div hd]
  rfl

/-- Quadratic-multiplicity capstone with the optimized rank coefficient
written in closed form.  The finite rank quotient is

`c d² / ((c d + 1) R)`,

which is asymptotic to `d / R`; the former generic rectangle supplied only
`d / (2R)`. -/
theorem total_contactEnvelope_finrank_lt_interpolationSpace_quadraticScalar
    {q c d A K B W C J R n : ℕ} [Fact (Nat.Prime q)]
    {widthCoefficient : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hn : 0 < n) (hR : 0 < R)
    (hJle : J ≤ quadraticMultiplicityAt c d)
    (hdegree : C + J ≤ B)
    (hweighted : (K - 1) * (C + J) ≤
      quadraticMultiplicityAt c d * A)
    (hshell : scaledExponentCount d
        (W + quadraticMultiplicityAt c d) ≤
      R * goodScaledExponentCount d W C)
    (hwidthCoefficient : 0 ≤ widthCoefficient)
    (hJlower : widthCoefficient * (quadraticMultiplicityAt c d : ℝ) ≤
      (J : ℝ))
    (hcompare :
      1 < (1 / 6) * widthCoefficient ^ 3 *
        (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (((c * d ^ 2 : ℕ) : ℝ) /
          (((c * d + 1 : ℕ) : ℝ) * (R : ℝ)))) :
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d)
            (quadraticMultiplicityAt c d) W) <
      Module.finrank (ZMod q)
          (interpolationSpace q d (quadraticMultiplicityAt c d)
            A K B W C) := by
  apply total_contactEnvelope_finrank_lt_interpolationSpace_of_divisibleScalar
    hd (quadraticMultiplicityAt_pos hc hd) hn hR
    (derivativeDepth_dvd_quadraticMultiplicityAt c d)
    hJle hdegree hweighted hshell hwidthCoefficient hJlower
  rw [quadratic_rank_quotient_eq hd]
  exact hcompare

/-! ## End-to-end rounded quadratic theorem -/

/-- The exact adaptive global sum at the rounded quadratic parameters. -/
noncomputable def quadraticAdaptiveGlobalCount
    (a : ℝ) (c d A K B : ℕ) : ℕ :=
  (K - 1) *
    ∑ e : ↥(goodHigherExponents d
      (quadraticShellWeight a c d) (quadraticShellDegree a c d)),
      (adaptiveGlobalSlack (quadraticMultiplicityAt c d) A K B e.1 + 2).choose 3

/-- The exact coupled local sum at the rounded quadratic parameters. -/
noncomputable def quadraticCoupledLocalCount
    (a : ℝ) (c d : ℕ) : ℕ :=
  coupledContactEnvelopeCount d (quadraticMultiplicityAt c d)
    (quadraticShellWeight a c d)

/-- A finite, end-to-end quadratic-multiplicity list-decoding theorem.

All rounding is internal to the displayed `quadraticShellWeight`,
`quadraticShellDegree`, and `adaptiveGlobalSlack` definitions.  The sole
combinatorial certificate is the comparison of the two exact weighted sums;
there is no uniform shell factor or minimum simplex width in the statement. -/
theorem quadratic_adaptive_listDecodable_of_exact_sum
    {q c d n k A K B : ℕ} {a : ℝ}
    (hq : Nat.Prime q) (hc : 0 < c) (hd : 0 < d)
    (hdK : d < K) (hkK : k ≤ K)
    (hKq : K ≤ q) (hB : 0 < B) (hBq : B < q)
    (hMq : quadraticMultiplicityAt c d * A ≤ q ^ 2)
    (hdegreeBudget : quadraticShellDegree a c d ≤ B)
    (hweightedBudget :
      (K - 1) * quadraticShellDegree a c d ≤
        quadraticMultiplicityAt c d * A)
    (hsums :
      n * quadraticCoupledLocalCount a c d <
        quadraticAdaptiveGlobalCount a c d A K B)
    (alpha : Fin n → ZMod q) (halpha : Function.Injective alpha) :
    IsListDecodableAtAgreement (k := k) hq.ne_zero alpha A
      (B * rootCountGeometricFactor q 2 d) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let m := quadraticMultiplicityAt c d
  let W := quadraticShellWeight a c d
  let C := quadraticShellDegree a c d
  let J : HigherJetExponent d → ℕ :=
    adaptiveGlobalSlack m A K B
  have hJ : ∀ e : ↥(goodHigherExponents d W C), J e.1 ≤ m :=
    fun e => adaptiveGlobalSlack_le_m e.1
  have hdegree : ∀ e : ↥(goodHigherExponents d W C),
      higherJetDegree e.1 + J e.1 ≤ B := by
    intro e
    apply higherJetDegree_add_adaptiveGlobalSlack_le_degreeBudget
    exact (mem_goodHigherExponents.mp e.2).2.trans hdegreeBudget
  have hweighted : ∀ e : ↥(goodHigherExponents d W C),
      (K - 1) * (higherJetDegree e.1 + J e.1) ≤ m * A := by
    intro e
    apply weighted_adaptiveGlobalSlack_le_budget (by omega)
    exact (Nat.mul_le_mul_left (K - 1)
      (mem_goodHigherExponents.mp e.2).2).trans hweightedBudget
  have hdim :
      n * Module.finrank (ZMod q)
          (coupledContactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C) := by
    apply total_coupledContactEnvelope_finrank_lt_interpolationSpace_adaptive
      hd hJ hdegree hweighted
    simpa [quadraticCoupledLocalCount, quadraticAdaptiveGlobalCount,
      m, W, C, J] using hsums
  have hA : 0 < A := by
    by_contra hA
    have hAz : A = 0 := Nat.eq_zero_of_not_pos hA
    have hright : quadraticAdaptiveGlobalCount a c d A K B = 0 := by
      simp [quadraticAdaptiveGlobalCount, adaptiveGlobalSlack, hAz]
    rw [hright] at hsums
    omega
  have hmA : 0 < m * A :=
    Nat.mul_pos (quadraticMultiplicityAt_pos hc hd) hA
  apply isListDecodableAtAgreement_sharp_of_ambient_explainers_of_le_dimension
    hq hdK hkK hKq hB hBq hMq alpha
  intro y
  apply exists_ambient_explainer_of_nonzero_interpolant
    hq (Nat.zero_lt_of_lt hdK) hmA alpha halpha y
  exact exists_nonzero_interpolant_satisfying_constraints_coupled
    hd hdim alpha y

/-- Base-field strengthening of `quadratic_adaptive_listDecodable_of_exact_sum`.
When the interpolation weighted-degree budget is at most `q`, the refined
root count avoids the quadratic extension and reduces the field exponent
from `2d+2` to `d+1`. -/
theorem quadratic_adaptive_listDecodable_baseField_of_exact_sum
    {q c d n k A K B : ℕ} {a : ℝ}
    (hq : Nat.Prime q) (hc : 0 < c) (hd : 0 < d)
    (hdK : d < K) (hkK : k ≤ K)
    (hKq : K ≤ q) (hB : 0 < B) (hBq : B < q)
    (hMq : quadraticMultiplicityAt c d * A ≤ q)
    (hdegreeBudget : quadraticShellDegree a c d ≤ B)
    (hweightedBudget :
      (K - 1) * quadraticShellDegree a c d ≤
        quadraticMultiplicityAt c d * A)
    (hsums :
      n * quadraticCoupledLocalCount a c d <
        quadraticAdaptiveGlobalCount a c d A K B)
    (alpha : Fin n → ZMod q) (halpha : Function.Injective alpha) :
    IsListDecodableAtAgreement (k := k) hq.ne_zero alpha A
      (B * rootCountGeometricFactor q 1 d) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let m := quadraticMultiplicityAt c d
  let W := quadraticShellWeight a c d
  let C := quadraticShellDegree a c d
  let J : HigherJetExponent d → ℕ :=
    adaptiveGlobalSlack m A K B
  have hJ : ∀ e : ↥(goodHigherExponents d W C), J e.1 ≤ m :=
    fun e => adaptiveGlobalSlack_le_m e.1
  have hdegree : ∀ e : ↥(goodHigherExponents d W C),
      higherJetDegree e.1 + J e.1 ≤ B := by
    intro e
    apply higherJetDegree_add_adaptiveGlobalSlack_le_degreeBudget
    exact (mem_goodHigherExponents.mp e.2).2.trans hdegreeBudget
  have hweighted : ∀ e : ↥(goodHigherExponents d W C),
      (K - 1) * (higherJetDegree e.1 + J e.1) ≤ m * A := by
    intro e
    apply weighted_adaptiveGlobalSlack_le_budget (by omega)
    exact (Nat.mul_le_mul_left (K - 1)
      (mem_goodHigherExponents.mp e.2).2).trans hweightedBudget
  have hdim :
      n * Module.finrank (ZMod q)
          (coupledContactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C) := by
    apply total_coupledContactEnvelope_finrank_lt_interpolationSpace_adaptive
      hd hJ hdegree hweighted
    simpa [quadraticCoupledLocalCount, quadraticAdaptiveGlobalCount,
      m, W, C, J] using hsums
  have hA : 0 < A := by
    by_contra hA
    have hAz : A = 0 := Nat.eq_zero_of_not_pos hA
    have hright : quadraticAdaptiveGlobalCount a c d A K B = 0 := by
      simp [quadraticAdaptiveGlobalCount, adaptiveGlobalSlack, hAz]
    rw [hright] at hsums
    omega
  have hmA : 0 < m * A :=
    Nat.mul_pos (quadraticMultiplicityAt_pos hc hd) hA
  apply isListDecodableAtAgreement_baseField_of_ambient_explainers_of_le_dimension
    hq hdK hkK hKq hB hBq hMq alpha
  intro y
  apply exists_ambient_explainer_of_nonzero_interpolant
    hq (Nat.zero_lt_of_lt hdK) hmA alpha halpha y
  exact exists_nonzero_interpolant_satisfying_constraints_coupled
    hd hdim alpha y

/-- Public finite statement for the rounded quadratic construction.  It is
phrased as an exact certificate theorem: the two explicitly computable
weighted counts are compared directly. -/
def QuadraticAdaptiveCombinatorialStatement : Prop :=
  ∀ a : ℝ, ∀ q c d n k A K B : ℕ,
    ∀ hq : Nat.Prime q,
      0 < c → 0 < d → d < K → k ≤ K → K ≤ q →
      0 < B → B < q →
      quadraticMultiplicityAt c d * A ≤ q ^ 2 →
      quadraticShellDegree a c d ≤ B →
      (K - 1) * quadraticShellDegree a c d ≤
        quadraticMultiplicityAt c d * A →
      n * quadraticCoupledLocalCount a c d <
        quadraticAdaptiveGlobalCount a c d A K B →
      ∀ alpha : Fin n → ZMod q, Function.Injective alpha →
        IsListDecodableAtAgreement (k := k) hq.ne_zero alpha A
          (B * rootCountGeometricFactor q 2 d)

theorem quadraticAdaptiveCombinatorialStatement_proved :
    QuadraticAdaptiveCombinatorialStatement := by
  intro a q c d n k A K B hq hc hd hdK hkK hKq hB hBq hMq
    hdegreeBudget hweightedBudget hsums alpha halpha
  exact quadratic_adaptive_listDecodable_of_exact_sum
    hq hc hd hdK hkK hKq hB hBq hMq hdegreeBudget hweightedBudget
      hsums alpha halpha

/-- Public finite statement for the base-field list-size optimization. -/
def QuadraticAdaptiveBaseFieldCombinatorialStatement : Prop :=
  ∀ a : ℝ, ∀ q c d n k A K B : ℕ,
    ∀ hq : Nat.Prime q,
      0 < c → 0 < d → d < K → k ≤ K → K ≤ q →
      0 < B → B < q →
      quadraticMultiplicityAt c d * A ≤ q →
      quadraticShellDegree a c d ≤ B →
      (K - 1) * quadraticShellDegree a c d ≤
        quadraticMultiplicityAt c d * A →
      n * quadraticCoupledLocalCount a c d <
        quadraticAdaptiveGlobalCount a c d A K B →
      ∀ alpha : Fin n → ZMod q, Function.Injective alpha →
        IsListDecodableAtAgreement (k := k) hq.ne_zero alpha A
          (B * rootCountGeometricFactor q 1 d)

theorem quadraticAdaptiveBaseFieldCombinatorialStatement_proved :
    QuadraticAdaptiveBaseFieldCombinatorialStatement := by
  intro a q c d n k A K B hq hc hd hdK hkK hKq hB hBq hMq
    hdegreeBudget hweightedBudget hsums alpha halpha
  exact quadratic_adaptive_listDecodable_baseField_of_exact_sum
    hq hc hd hdK hkK hKq hB hBq hMq hdegreeBudget hweightedBudget
      hsums alpha halpha

end RSListDecoding
