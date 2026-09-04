import RSListDecoding.Defs.FieldOperationCost
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# A costed homogeneous linear-system solver

The solver below is a recursive form of Gaussian elimination specialized to
the only case needed by interpolation: a matrix with strictly more columns
than rows.  On a nonzero first row it chooses a pivot, eliminates that
variable from the remaining rows, recursively solves the smaller system, and
then reconstructs the pivot coordinate.  On a zero first row it simply drops
that row.

The result and the charged operation count are defined together.  Pivot
search charges one field equality test per column.  Forming each entry of the
Schur-style reduced matrix charges two multiplications and one subtraction;
the inverse is computed once.  Reconstructing the pivot coordinate charges
the displayed dot-product operations.  The companion lemmas prove that the
returned vector is nonzero, lies in the kernel, and satisfies a cubic bound.
-/

open scoped BigOperators

namespace RSListDecoding

namespace GaussianKernel

/-- The only inverse law used by Gaussian elimination.  Keeping this law in a
proposition-valued class avoids the incompatible `CommRing`/`Field` instance
diamond that otherwise appears for `ZMod q` inside module-valued types. -/
class LawfulFieldInverse (F : Type*) [CommRing F] [Inv F] : Prop where
  mul_inv_cancel_of_ne_zero : ∀ {a : F}, a ≠ 0 → a * a⁻¹ = 1

variable {F : Type*} [CommRing F] [Inv F] [DecidableEq F]

/-- The matrix left after eliminating pivot column `p` from the first row. -/
def reduceAtPivot {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) F)
    (p : Fin (n + 1)) : Matrix (Fin m) (Fin n) F :=
  fun i j ↦
    A i.succ (p.succAbove j) -
      A i.succ p * (A 0 p)⁻¹ * A 0 (p.succAbove j)

/-- Reinsert the pivot coordinate so the first row has dot product zero. -/
def liftAtPivot {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) F)
    (p : Fin (n + 1)) (z : Fin n → F) : Fin (n + 1) → F :=
  Fin.insertNth p
    (-((A 0 p)⁻¹ * ∑ j : Fin n, A 0 (p.succAbove j) * z j)) z

/-- The exact charged cost used by the recursive solver.

The definition deliberately charges a full scan of every first row, even if
the selected pivot occurs earlier.  This gives a simple deterministic upper
bound while remaining a valid implementation cost. -/
def solve : (m n : ℕ) → m < n →
    Matrix (Fin m) (Fin n) F → FieldCost (Fin n → F)
  | 0, 0, h, _ => nomatch h
  | 0, n + 1, _, _ =>
      FieldCost.pure (fun j ↦ if j = (0 : Fin (n + 1)) then 1 else 0)
  | m + 1, 0, h, _ => nomatch h
  | m + 1, n + 1, h, A =>
      if hpivot : ∃ p : Fin (n + 1), A 0 p ≠ 0 then
        let p := Fin.find (fun j ↦ A 0 j ≠ 0) hpivot
        let reduced := reduceAtPivot A p
        let recursive := solve m n (by omega) reduced
        ⟨liftAtPivot A p recursive.result,
          (n + 1) + 1 + 3 * m * n + recursive.operations + (2 * n + 2)⟩
      else
        let tail : Matrix (Fin m) (Fin (n + 1)) F := fun i j ↦ A i.succ j
        let recursive := solve m (n + 1) (by omega) tail
        ⟨recursive.result, (n + 1) + recursive.operations⟩
termination_by m n _ _ => m

end GaussianKernel

end RSListDecoding
