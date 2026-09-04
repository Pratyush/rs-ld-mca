import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RSListDecoding.Defs.DifferentialEquation

/-!
# Integer parameters in the combinatorial theorem

These are the rounded parameters used in the manuscript, with `K` serving as
the ambient interpolation dimension.  Separating `K` from the requested code
dimension `k ≤ K` makes the lower-rate result a subcode consequence.
-/

namespace RSListDecoding

/-- Maximum Hasse-derivative order `d = ceil(ε^(-3/θ))`. -/
noncomputable def derivativeOrder (ε θ : ℝ) : ℕ :=
  ⌈ε ^ (-3 / θ)⌉₊

/-- Multiplicity as a function of a freely chosen derivative order. -/
def multiplicityAt (d : ℕ) : ℕ := d ^ 3

/-- Multiplicity parameter `m = d^3`. -/
noncomputable def multiplicity (ε θ : ℝ) : ℕ :=
  derivativeOrder ε θ ^ 3

/-- Integer agreement threshold `A = ceil(ε n)`. -/
noncomputable def agreementThreshold (ε : ℝ) (n : ℕ) : ℕ :=
  ⌈ε * n⌉₊

/-- Ambient interpolation dimension `K = floor((1-θ) ε n)`. -/
noncomputable def ambientDimension (ε θ : ℝ) (n : ℕ) : ℕ :=
  ⌊(1 - θ) * ε * n⌋₊

/-- Interpolation degree budget `B = ceil(m A / (K-1))`.  The capstone
statement assumes `d < K`, so the displayed denominator is positive. -/
noncomputable def interpolationDegreeBudgetAt
    (d : ℕ) (ε θ : ℝ) (n : ℕ) : ℕ :=
  ⌈(((multiplicityAt d * agreementThreshold ε n : ℕ) : ℝ) /
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ))⌉₊

noncomputable def interpolationDegreeBudget (ε θ : ℝ) (n : ℕ) : ℕ :=
  ⌈(((multiplicity ε θ * agreementThreshold ε n : ℕ) : ℝ) /
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ))⌉₊

/-- Anisotropic higher-jet budget
`W = floor ((1+θ/2) d m / log(e d))`.

We write the denominator as `1 + log d`, equal to `log(e d)` for positive
`d`.  This form avoids carrying the transcendental constant `e` through the
integer estimates. -/
noncomputable def interpolationWeightBudgetAt (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊((1 + θ / 2) * (d : ℝ) * (multiplicityAt d : ℝ)) /
      (1 + Real.log (d : ℝ))⌋₊

noncomputable def interpolationWeightBudget (ε θ : ℝ) : ℕ :=
  ⌊((1 + θ / 2) * (derivativeOrder ε θ : ℝ) *
      (multiplicity ε θ : ℝ)) /
      (1 + Real.log (derivativeOrder ε θ : ℝ))⌋₊

/-- Ordinary higher-jet cutoff.  The formalization and repaired manuscript
consistently use the floor convention (MF-004). -/
noncomputable def higherJetDegreeBudgetAt (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊(1 + 3 * θ / 4) * (multiplicityAt d : ℝ)⌋₊

noncomputable def higherJetDegreeBudget (ε θ : ℝ) : ℕ :=
  ⌊(1 + 3 * θ / 4) * (multiplicity ε θ : ℝ)⌋₊

/-- Width of each coordinate in the free-order rectangular family. -/
noncomputable def interpolationBoxWidthAt (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊θ * (multiplicityAt d : ℝ) / 12⌋₊

/-- Former conservative total slack of the global simplex. -/
noncomputable def interpolationSimplexWidthAt (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊θ * (multiplicityAt d : ℝ) / 4⌋₊

/-- Largest uniform fraction of the multiplicity budget available to the
global slack simplex under the current higher-jet cutoff.  The outer minimum
enforces the independent requirement that the first slack coordinate be
smaller than the multiplicity. -/
noncomputable def optimizedSimplexSlackCoefficient (θ : ℝ) : ℝ :=
  min 1 (θ * (1 + 3 * θ) / (4 * (1 - θ)))

/-- Limiting normalized volume of the optimized three-dimensional slack
simplex. -/
noncomputable def optimizedSimplexVolumeCoefficient (θ : ℝ) : ℝ :=
  optimizedSimplexSlackCoefficient θ ^ 3 / 6

/-- Directly rounded maximal global-simplex width. -/
noncomputable def optimizedInterpolationSimplexWidthAt
    (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊optimizedSimplexSlackCoefficient θ * (multiplicityAt d : ℝ)⌋₊

/-- Original manuscript width, retained by the original capstones. -/
noncomputable def interpolationBoxWidth (ε θ : ℝ) : ℕ :=
  ⌊θ * (multiplicity ε θ : ℝ) / 16⌋₊

/-- Public list-size bound from the refined quadratic-extension root count. -/
def publicListBoundAt (q d : ℕ) : ℕ :=
  q ^ (2 * d + 4)

/-- Exact refined root-counting bound for the free-order theorem, before
absorbing the two polynomial prefactors into powers of the field size. -/
noncomputable def sharpListBoundAt
    (q d : ℕ) (ε θ : ℝ) (n : ℕ) : ℕ :=
  interpolationDegreeBudgetAt d ε θ n * rootCountGeometricFactor q 2 d

/-- Stronger exact list bound when the interpolation weighted degree is
strictly below the base-field size. -/
noncomputable def baseFieldSharpListBoundAt
    (q d : ℕ) (ε θ : ℝ) (n : ℕ) : ℕ :=
  interpolationDegreeBudgetAt d ε θ n * rootCountGeometricFactor q 1 d

/-- Absorbed public form of the base-field list bound. -/
def baseFieldPublicListBoundAt (q d : ℕ) : ℕ :=
  q ^ (d + 3)

noncomputable def publicListBound (q : ℕ) (ε θ : ℝ) : ℕ :=
  q ^ (2 * derivativeOrder ε θ + 4)

end RSListDecoding
