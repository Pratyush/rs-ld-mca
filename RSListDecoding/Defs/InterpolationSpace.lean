import RSListDecoding.Defs.DifferentialEquation
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The global interpolation space

This module encodes the monomial support in `eq:global-space` parametrically
in the two higher-jet budgets.  The natural numbers `W` and `C` remain
explicit so the algebraic API is independent of later rounded estimates.

An exponent of a differential polynomial is a finitely supported function on
`JetVariable d`: `none` is the exponent of `X`, while `some j` is the exponent
of `Y_j`.  We first define the finite anisotropic set for the variables
`Y₂, ..., Y_d`, then impose the complete collection of global support
constraints directly on full exponents.  Finally, the interpolation space is
the `ZMod q`-submodule whose polynomial supports lie in that finite set.
-/

noncomputable section

namespace RSListDecoding

/-- Exponent vectors for the higher jet variables `Y₂, ..., Y_d`.

The coordinate `i : Fin (d - 1)` represents `Y_{i+2}`.  This convention is
total also for `d = 0` and `d = 1`, when the type has no coordinates. -/
abbrev HigherJetExponent (d : ℕ) := Fin (d - 1) →₀ ℕ

/-- The anisotropic weight `ω(c) = ∑ᵢ (i+1)cᵢ` on the exponents of
`Y₂, ..., Y_d`. -/
def higherJetWeight {d : ℕ} (c : HigherJetExponent d) : ℕ :=
  Finsupp.weight (fun i : Fin (d - 1) => i.val + 1) c

/-- The ordinary degree `|c|` of a higher-jet exponent vector. -/
def higherJetDegree {d : ℕ} (c : HigherJetExponent d) : ℕ :=
  Finsupp.degree c

/-- Predicate defining the anisotropically bounded set of higher-jet
exponents.  `C` is kept separate from `W` so changes to rounded estimates do
not affect this algebraic API. -/
def GoodHigherExponent (d W C : ℕ) (c : HigherJetExponent d) : Prop :=
  higherJetWeight c ≤ W ∧ higherJetDegree c ≤ C

/-- The set underlying `goodHigherExponents`. -/
def goodHigherExponentSet (d W C : ℕ) : Set (HigherJetExponent d) :=
  {c | GoodHigherExponent d W C c}

/-- There are only finitely many higher-jet exponents of bounded anisotropic
weight.  In particular, adding the ordinary-degree cutoff preserves
finiteness. -/
theorem goodHigherExponentSet_finite (d W C : ℕ) :
    (goodHigherExponentSet d W C).Finite := by
  apply (Finsupp.finite_of_nat_weight_le
    (fun i : Fin (d - 1) => i.val + 1) (by omega) W).subset
  intro c hc
  exact hc.1

/-- The finite anisotropic exponent set `𝒢` for `Y₂, ..., Y_d`. -/
def goodHigherExponents (d W C : ℕ) : Finset (HigherJetExponent d) :=
  (goodHigherExponentSet_finite d W C).toFinset

@[simp]
theorem mem_goodHigherExponents {d W C : ℕ} {c : HigherJetExponent d} :
    c ∈ goodHigherExponents d W C ↔ GoodHigherExponent d W C c := by
  simp [goodHigherExponents, goodHigherExponentSet]

/-- The exponent of `Y₁`, written as a weight so that the definition remains
total when `d = 0` and there is no `Y₁` coordinate. -/
def firstJetExponent {d : ℕ} (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (fun j : Fin (d + 1) => if j.val = 1 then 1 else 0) u.some

/-- The total exponent of all jet variables `Y₀, ..., Y_d`. -/
def totalJetDegree {d : ℕ} (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.degree u.some

/-- The anisotropic weight on the higher coordinates of a full exponent.
Coordinates `Y₀` and `Y₁` have weight zero and `Y_j` has weight `j-1`. -/
def fullHigherJetWeight {d : ℕ} (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (fun j : Fin (d + 1) => j.val - 1) u.some

/-- The ordinary degree in the higher variables `Y₂, ..., Y_d`, expressed as
a weight on a full exponent vector. -/
def fullHigherJetDegree {d : ℕ} (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (fun j : Fin (d + 1) => if 2 ≤ j.val then 1 else 0) u.some

/-- A full monomial exponent satisfying the corrected, support-first version
of `eq:global-space`.

The five clauses respectively say

* the `Y₁` exponent is at most `m`;
* the total jet degree is at most `B`;
* the `(1,K-1,...,K-1)` weighted degree is strictly below `mA`;
* the higher-jet anisotropic weight is at most `W`; and
* the higher-jet ordinary degree is at most `C`.
-/
def GlobalEligibleExponent (d m A K B W C : ℕ)
    (u : JetVariable d →₀ ℕ) : Prop :=
  firstJetExponent u ≤ m ∧
    totalJetDegree u ≤ B ∧
    u none + (K - 1) * totalJetDegree u < m * A ∧
    fullHigherJetWeight u ≤ W ∧
    fullHigherJetDegree u ≤ C

/-- The set underlying `globalEligibleExponents`. -/
def globalEligibleExponentSet (d m A K B W C : ℕ) :
    Set (JetVariable d →₀ ℕ) :=
  {u | GlobalEligibleExponent d m A K B W C u}

/-- Splitting an exponent on an `Option` domain separates the exponent of
`X` from the total jet degree. -/
theorem exponentDegree_eq_x_add_totalJetDegree {d : ℕ}
    (u : JetVariable d →₀ ℕ) :
    Finsupp.degree u = u none + totalJetDegree u := by
  classical
  simp [Finsupp.degree_eq_sum, totalJetDegree, Fintype.sum_option]

/-- The complete set of eligible exponents is finite.  The global weighted
degree bounds the `X` exponent, and the separate jet-degree clause bounds all
remaining coordinates. -/
theorem globalEligibleExponentSet_finite (d m A K B W C : ℕ) :
    (globalEligibleExponentSet d m A K B W C).Finite := by
  apply (Finsupp.finite_of_degree_le (m * A + B)).subset
  intro u hu
  have hxlt : u none < m * A :=
    lt_of_le_of_lt (Nat.le_add_right (u none) ((K - 1) * totalJetDegree u)) hu.2.2.1
  change Finsupp.degree u ≤ m * A + B
  rw [exponentDegree_eq_x_add_totalJetDegree]
  exact Nat.add_le_add (Nat.le_of_lt hxlt) hu.2.1

/-- The finite set of all monomial exponents allowed in the global
interpolation space. -/
def globalEligibleExponents (d m A K B W C : ℕ) :
    Finset (JetVariable d →₀ ℕ) :=
  (globalEligibleExponentSet_finite d m A K B W C).toFinset

@[simp]
theorem mem_globalEligibleExponents {d m A K B W C : ℕ}
    {u : JetVariable d →₀ ℕ} :
    u ∈ globalEligibleExponents d m A K B W C ↔
      GlobalEligibleExponent d m A K B W C u := by
  simp [globalEligibleExponents, globalEligibleExponentSet]

/-- The global interpolation submodule over `ZMod q`: precisely the
polynomials supported on eligible monomials. -/
def interpolationSpace (q d m A K B W C : ℕ) :
    Submodule (ZMod q) (DifferentialPolynomial q d) :=
  MvPolynomial.restrictSupport (ZMod q)
    (↑(globalEligibleExponents d m A K B W C) : Set (JetVariable d →₀ ℕ))

/-- Membership in the interpolation space is exactly pointwise eligibility
of every exponent in the polynomial support. -/
theorem mem_interpolationSpace_iff {q d m A K B W C : ℕ}
    {Q : DifferentialPolynomial q d} :
    Q ∈ interpolationSpace q d m A K B W C ↔
      ∀ u ∈ Q.support, GlobalEligibleExponent d m A K B W C u := by
  rw [interpolationSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_globalEligibleExponents]

/-- Set-theoretic form of `mem_interpolationSpace_iff`, useful for invoking
the generic `restrictSupport` API. -/
theorem mem_interpolationSpace_iff_support_subset {q d m A K B W C : ℕ}
    {Q : DifferentialPolynomial q d} :
    Q ∈ interpolationSpace q d m A K B W C ↔
      (↑Q.support : Set (JetVariable d →₀ ℕ)) ⊆
        ↑(globalEligibleExponents d m A K B W C) := by
  rfl

/-- A nonzero monomial belongs to the interpolation space exactly when its
exponent is eligible. -/
@[simp]
theorem monomial_mem_interpolationSpace {q d m A K B W C : ℕ}
    {u : JetVariable d →₀ ℕ} {a : ZMod q} :
    MvPolynomial.monomial u a ∈ interpolationSpace q d m A K B W C ↔
      GlobalEligibleExponent d m A K B W C u ∨ a = 0 := by
  simp [interpolationSpace]

/-- The canonical monomial basis of the global interpolation space.  Its
index type is the subtype of the finite eligible exponent set. -/
def interpolationSpaceBasis (q d m A K B W C : ℕ) :=
  MvPolynomial.basisRestrictSupport (R := ZMod q)
    (↑(globalEligibleExponents d m A K B W C) : Set (JetVariable d →₀ ℕ))

end RSListDecoding
