import RSListDecoding.Lemmas.GaussianKernel
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Costed common kernels in finite coordinates

This module turns the checked matrix solver into the basis-independent form
needed by interpolation.  A finite family of linear maps is written as one
block matrix using supplied bases.  If the total number of rows is smaller
than the number of columns, Gaussian elimination returns a nonzero vector
annihilated by every map.
-/

namespace RSListDecoding

open GaussianKernel

variable {F : Type*} [CommRing F] [Inv F] [DecidableEq F]
variable {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
variable [DecidableEq κ]
variable {V W : Type*}
variable [AddCommGroup V] [Module F V]
variable [AddCommGroup W] [Module F W]

/-- The block matrix of a finite family of linear maps. -/
noncomputable def linearFamilyMatrix (bV : Module.Basis κ F V)
    (bW : Module.Basis ρ F W) (φ : ι → V →ₗ[F] W) :
    Matrix (ι × ρ) κ F :=
  fun row col ↦ LinearMap.toMatrix bV bW (φ row.1) row.2 col

/-- Solve all maps in the family simultaneously. -/
noncomputable def solveLinearFamily (bV : Module.Basis κ F V)
    (bW : Module.Basis ρ F W) (φ : ι → V →ₗ[F] W)
    (h : Fintype.card (ι × ρ) < Fintype.card κ) : FieldCost V :=
  FieldCost.map bV.equivFun.symm
    (solveFintype h (linearFamilyMatrix bV bW φ))

@[simp]
theorem solveLinearFamily_operations (bV : Module.Basis κ F V)
    (bW : Module.Basis ρ F W) (φ : ι → V →ₗ[F] W)
    (h : Fintype.card (ι × ρ) < Fintype.card κ) :
    (solveLinearFamily bV bW φ h).operations =
      (solveFintype h (linearFamilyMatrix bV bW φ)).operations := rfl

theorem solveLinearFamily_result_ne_zero [Nontrivial F]
    [LawfulFieldInverse F] (bV : Module.Basis κ F V)
    (bW : Module.Basis ρ F W) (φ : ι → V →ₗ[F] W)
    (h : Fintype.card (ι × ρ) < Fintype.card κ) :
    (solveLinearFamily bV bW φ h).result ≠ 0 := by
  have hc := solveFintype_result_ne_zero h (linearFamilyMatrix bV bW φ)
  intro hv
  apply hc
  exact bV.equivFun.symm.map_eq_zero_iff.mp (by
    simpa [solveLinearFamily] using hv)

theorem solveLinearFamily_result_mem_kernels
    [Nontrivial F] [LawfulFieldInverse F]
    (bV : Module.Basis κ F V) (bW : Module.Basis ρ F W)
    (φ : ι → V →ₗ[F] W)
    (h : Fintype.card (ι × ρ) < Fintype.card κ) :
    ∀ i, φ i (solveLinearFamily bV bW φ h).result = 0 := by
  intro i
  let c := (solveFintype h (linearFamilyMatrix bV bW φ)).result
  let v := bV.equivFun.symm c
  have hmatrix := solveFintype_result_mem_kernel h
    (linearFamilyMatrix bV bW φ)
  apply bW.repr.injective
  ext j
  have hrow := congrFun hmatrix (i, j)
  have hcoordinate := congrFun
    (LinearMap.toMatrix_mulVec_repr bV bW (φ i) v) j
  have hcoeff : ⇑(bV.repr v) = c := by
    funext a
    exact bV.coord_equivFun_symm a c
  change bW.repr (φ i v) j = bW.repr 0 j
  rw [map_zero, Finsupp.zero_apply]
  rw [← hcoordinate]
  rw [hcoeff]
  change (linearFamilyMatrix bV bW φ).mulVec c (i, j) = 0
  exact hrow

theorem solveLinearFamily_operations_le
    (bV : Module.Basis κ F V) (bW : Module.Basis ρ F W)
    (φ : ι → V →ₗ[F] W)
    (h : Fintype.card (ι × ρ) < Fintype.card κ) :
    (solveLinearFamily bV bW φ h).operations ≤
      8 * Fintype.card (ι × ρ) * Fintype.card κ ^ 2 +
        Fintype.card κ := by
  exact solveFintype_operations_le h (linearFamilyMatrix bV bW φ)

end RSListDecoding
