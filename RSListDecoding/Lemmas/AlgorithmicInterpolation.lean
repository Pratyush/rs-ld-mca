import RSListDecoding.Lemmas.CostedLinearKernel
import RSListDecoding.Lemmas.InterpolationKernel

/-!
# Algorithmic interpolation in canonical monomial coordinates

The combinatorial proof obtained an interpolant by abstract dimension theory.
Here the same finite spaces are equipped with their canonical monomial bases,
the point constraints are assembled into an explicit block matrix, and the
checked Gaussian solver computes a nonzero common-kernel vector.

This module charges the elimination phase.  The separate constraint-building
module accounts for evaluating the matrix entries from `(alpha,y)`; keeping
the two phases separate prevents matrix construction from disappearing inside
the linear-algebra abstraction.
-/

noncomputable section

namespace RSListDecoding

instance {q : ℕ} [Fact (Nat.Prime q)] :
    GaussianKernel.LawfulFieldInverse (ZMod q) where
  mul_inv_cancel_of_ne_zero := by
    intro a ha
    exact mul_inv_cancel₀ ha

/-- Canonical column indices for the global interpolation space. -/
abbrev InterpolationColumn (d m A K B W C : ℕ) :=
  {u : JetVariable d →₀ ℕ //
    u ∈ (↑(globalEligibleExponents d m A K B W C) :
      Set (JetVariable d →₀ ℕ))}

/-- Canonical monomial coordinates for the finite local contact envelope. -/
abbrev ContactEnvelopeCoordinate (d m W : ℕ) :=
  {e : LocalVariable d →₀ ℕ // ContactEnvelopeExponent (d := d) m W e}

/-- The positive-depth contact envelope is explicitly finite, via the
injection used in the checked rank count. -/
@[reducible] def contactEnvelopeCoordinateFintype {d m W : ℕ} (hd : 0 < d) :
    Fintype (ContactEnvelopeCoordinate d m W) :=
  Fintype.ofInjective (encodeContactEnvelope (m := m) (W := W) hd)
    (encodeContactEnvelope_injective (m := m) (W := W) hd)

/-- Canonical monomial basis of the finite local contact envelope. -/
def contactEnvelopeBasis (R : Type*) [CommRing R] (d m W : ℕ) :
    Module.Basis (ContactEnvelopeCoordinate d m W) R
      (contactEnvelopeSpace (R := R) (d := d) m W) :=
  MvPolynomial.basisRestrictSupport R
    {e | ContactEnvelopeExponent (d := d) m W e}

/-- The explicit interpolation constraint matrix.  A row is a received point
together with one contact-envelope monomial; a column is one eligible global
monomial. -/
def interpolationConstraintMatrix {q d m A K B W C n : ℕ}
    [Fact (Nat.Prime q)]
    [Fintype (ContactEnvelopeCoordinate d m W)]
    (alpha y : Fin n → ZMod q) :
    Matrix (Fin n × ContactEnvelopeCoordinate d m W)
      (InterpolationColumn d m A K B W C) (ZMod q) :=
  linearFamilyMatrix
    (interpolationSpaceBasis q d m A K B W C)
    (contactEnvelopeBasis (ZMod q) d m W)
    (fun i ↦ pointConstraintMap (alpha i) (y i))

/-- A conservative operation allowance for one constraint-matrix entry.

The direct expansion has at most `mA+1` possible `T` exponents from the
translated `X` power and at most `(B+d+2)^(d+2)` distributions of the `Y₀`
power among its `d+2` summands.  The final square pays for generating powers,
multinomial coefficients, coefficient products, and accumulation. -/
def interpolationEntryOperations (d m A B : ℕ) : ℕ :=
  (m * A + 1) * (B + d + 2) ^ (d + 2) *
    (m * A + B + d + 3) ^ 2

/-- Charged work for explicitly constructing every entry of the block
constraint matrix.  `K` and `C` affect which columns are present, even though
the per-entry expansion allowance does not depend on them. -/
def interpolationMatrixOperationsFull
    (n d m A K B W C : ℕ) : ℕ :=
  (n * Nat.card (ContactEnvelopeCoordinate d m W)) *
    Nat.card (InterpolationColumn d m A K B W C) *
      interpolationEntryOperations d m A B

private theorem interpolation_card_lt
    {q d m A K B W C n : ℕ} [Fact (Nat.Prime q)]
    [Fintype (ContactEnvelopeCoordinate d m W)]
    (hdim :
      n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C)) :
    Fintype.card (Fin n × ContactEnvelopeCoordinate d m W) <
      Fintype.card (InterpolationColumn d m A K B W C) := by
  let sourceBasis := interpolationSpaceBasis q d m A K B W C
  let targetBasis := contactEnvelopeBasis (ZMod q) d m W
  rw [Fintype.card_prod, Fintype.card_fin]
  calc
    n * Fintype.card (ContactEnvelopeCoordinate d m W) =
        n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) := by
      rw [Module.finrank_eq_card_basis targetBasis]
    _ < Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C) := hdim
    _ = Fintype.card (InterpolationColumn d m A K B W C) := by
      exact Module.finrank_eq_card_basis sourceBasis

/-- Compute a nonzero interpolant by Gaussian elimination on the explicit
constraint matrix.  This is the algorithmic replacement for the
`Classical.choice`-based existence step in the combinatorial proof. -/
def solveInterpolationConstraints {q d m A K B W C n : ℕ}
    [Fact (Nat.Prime q)] (hd : 0 < d)
    (hdim :
      n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C))
    (alpha y : Fin n → ZMod q) :
    FieldCost (interpolationSpace q d m A K B W C) := by
  letI : Fintype (ContactEnvelopeCoordinate d m W) :=
    contactEnvelopeCoordinateFintype hd
  let sourceBasis := interpolationSpaceBasis q d m A K B W C
  let targetBasis := contactEnvelopeBasis (ZMod q) d m W
  have hcard := interpolation_card_lt hdim
  let solution := solveLinearFamily sourceBasis targetBasis
    (fun i ↦ pointConstraintMap (alpha i) (y i)) hcard
  exact ⟨solution.result,
    interpolationMatrixOperationsFull n d m A K B W C +
      solution.operations⟩

/-- The computed interpolation-space vector is nonzero. -/
theorem solveInterpolationConstraints_ne_zero
    {q d m A K B W C n : ℕ} [Fact (Nat.Prime q)] (hd : 0 < d)
    (hdim :
      n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C))
    (alpha y : Fin n → ZMod q) :
    (solveInterpolationConstraints hd hdim alpha y).result ≠ 0 := by
  letI : Fintype (ContactEnvelopeCoordinate d m W) :=
    contactEnvelopeCoordinateFintype hd
  let sourceBasis := interpolationSpaceBasis q d m A K B W C
  let targetBasis := contactEnvelopeBasis (ZMod q) d m W
  have hcard := interpolation_card_lt hdim
  change (solveLinearFamily sourceBasis targetBasis
    (fun i ↦ pointConstraintMap (alpha i) (y i)) hcard).result ≠ 0
  exact solveLinearFamily_result_ne_zero sourceBasis targetBasis _ hcard

/-- Every point constraint vanishes on the computed interpolant. -/
theorem solveInterpolationConstraints_satisfies
    {q d m A K B W C n : ℕ} [Fact (Nat.Prime q)] (hd : 0 < d)
    (hdim :
      n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C))
    (alpha y : Fin n → ZMod q) :
    ∀ i : Fin n,
      SatisfiesLocalConstraints m (alpha i) (y i)
        (solveInterpolationConstraints hd hdim alpha y).result.1 := by
  letI : Fintype (ContactEnvelopeCoordinate d m W) :=
    contactEnvelopeCoordinateFintype hd
  let sourceBasis := interpolationSpaceBasis q d m A K B W C
  let targetBasis := contactEnvelopeBasis (ZMod q) d m W
  have hcard := interpolation_card_lt hdim
  intro i
  apply (pointConstraintMap_eq_zero_iff_satisfiesLocalConstraints
    (alpha i) (y i) _).mp
  change (pointConstraintMap (alpha i) (y i))
    (solveLinearFamily sourceBasis targetBasis
      (fun j ↦ pointConstraintMap (alpha j) (y j)) hcard).result = 0
  exact solveLinearFamily_result_mem_kernels sourceBasis targetBasis
    (φ := fun j ↦ pointConstraintMap (alpha j) (y j)) hcard i

/-- Exact matrix-construction plus Gaussian-elimination cost bound for the
interpolation phase, stated in canonical coordinate counts. -/
theorem solveInterpolationConstraints_operations_le
    {q d m A K B W C n : ℕ} [Fact (Nat.Prime q)] (hd : 0 < d)
    (hdim :
      n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C))
    (alpha y : Fin n → ZMod q) :
    (solveInterpolationConstraints hd hdim alpha y).operations ≤
      interpolationMatrixOperationsFull n d m A K B W C +
      (8 *
          (n * Nat.card (ContactEnvelopeCoordinate d m W)) *
          Nat.card (InterpolationColumn d m A K B W C) ^ 2 +
        Nat.card (InterpolationColumn d m A K B W C)) := by
  letI : Fintype (ContactEnvelopeCoordinate d m W) :=
    contactEnvelopeCoordinateFintype hd
  let sourceBasis := interpolationSpaceBasis q d m A K B W C
  let targetBasis := contactEnvelopeBasis (ZMod q) d m W
  have hcard := interpolation_card_lt hdim
  change interpolationMatrixOperationsFull n d m A K B W C +
      (solveLinearFamily sourceBasis targetBasis
        (fun i ↦ pointConstraintMap (alpha i) (y i)) hcard).operations ≤ _
  have hcost := solveLinearFamily_operations_le sourceBasis targetBasis
    (fun i ↦ pointConstraintMap (alpha i) (y i)) hcard
  apply Nat.add_le_add_left
  simpa only [InterpolationColumn, Fintype.card_prod, Fintype.card_fin,
    Nat.card_eq_fintype_card] using hcost

end RSListDecoding
