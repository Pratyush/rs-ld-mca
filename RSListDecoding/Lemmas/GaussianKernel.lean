import RSListDecoding.Defs.GaussianKernel
import Mathlib.Tactic

/-!
# Correctness and cost of the homogeneous solver

These proofs justify the internal interpolation solver.  No linear-algebra
algorithm is assumed: correctness follows by induction over the rows of the
matrix and the cost follows from the recurrence in `GaussianKernel.solve`.
-/

open scoped BigOperators

namespace RSListDecoding

namespace GaussianKernel

variable {F : Type*} [CommRing F] [Inv F]

@[simp]
theorem liftAtPivot_apply_pivot {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) F)
    (p : Fin (n + 1)) (z : Fin n → F) :
    liftAtPivot A p z p =
      -((A 0 p)⁻¹ * ∑ j : Fin n, A 0 (p.succAbove j) * z j) := by
  simp [liftAtPivot]

@[simp]
theorem liftAtPivot_apply_free {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) F)
    (p : Fin (n + 1)) (z : Fin n → F) (j : Fin n) :
    liftAtPivot A p z (p.succAbove j) = z j := by
  simp [liftAtPivot]

theorem liftAtPivot_ne_zero {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) F)
    (p : Fin (n + 1)) {z : Fin n → F} (hz : z ≠ 0) :
    liftAtPivot A p z ≠ 0 := by
  intro hzero
  apply hz
  funext j
  have := congrFun hzero (p.succAbove j)
  simpa using this

theorem firstRow_mulVec_liftAtPivot [LawfulFieldInverse F] {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) F)
    (p : Fin (n + 1)) (hp : A 0 p ≠ 0) (z : Fin n → F) :
    A.mulVec (liftAtPivot A p z) 0 = 0 := by
  rw [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_succAbove _ p]
  simp only [liftAtPivot_apply_pivot, liftAtPivot_apply_free]
  change
    A 0 p * (-((A 0 p)⁻¹ * ∑ j : Fin n,
      A 0 (p.succAbove j) * z j)) +
      ∑ j : Fin n, A 0 (p.succAbove j) * z j = 0
  rw [mul_neg, ← mul_assoc,
    LawfulFieldInverse.mul_inv_cancel_of_ne_zero hp, one_mul]
  exact neg_add_cancel _

theorem tailRow_mulVec_liftAtPivot {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) F)
    (p : Fin (n + 1)) (z : Fin n → F) (i : Fin m) :
    A.mulVec (liftAtPivot A p z) i.succ =
      (reduceAtPivot A p).mulVec z i := by
  rw [Matrix.mulVec_apply, Matrix.mulVec_apply, dotProduct,
    Fin.sum_univ_succAbove _ p]
  simp only [liftAtPivot_apply_pivot, liftAtPivot_apply_free]
  change
    A i.succ p * (-((A 0 p)⁻¹ * ∑ j : Fin n,
      A 0 (p.succAbove j) * z j)) +
      ∑ j : Fin n, A i.succ (p.succAbove j) * z j =
    ∑ j : Fin n,
      (A i.succ (p.succAbove j) -
        A i.succ p * (A 0 p)⁻¹ * A 0 (p.succAbove j)) * z j
  simp only [Finset.sum_sub_distrib, sub_mul]
  have hfactor :
      (∑ x : Fin n,
        A i.succ p * (A 0 p)⁻¹ * A 0 (p.succAbove x) * z x) =
        A i.succ p * (A 0 p)⁻¹ *
          ∑ x : Fin n, A 0 (p.succAbove x) * z x := by
    calc
      _ = ∑ x : Fin n,
          (A i.succ p * (A 0 p)⁻¹) *
            (A 0 (p.succAbove x) * z x) := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = _ := (Finset.mul_sum Finset.univ
        (fun x : Fin n ↦ A 0 (p.succAbove x) * z x)
        (A i.succ p * (A 0 p)⁻¹)).symm
  rw [hfactor]
  ring

variable [DecidableEq F]

/-- The internal solver always returns a nonzero vector in the kernel. -/
theorem solve_spec [Nontrivial F] [LawfulFieldInverse F] :
    ∀ (m n : ℕ) (h : m < n) (A : Matrix (Fin m) (Fin n) F),
      (solve m n h A).result ≠ 0 ∧
        A.mulVec (solve m n h A).result = 0 := by
  intro m
  induction m with
  | zero =>
      intro n h A
      cases n with
      | zero => omega
      | succ n =>
          constructor
          · intro hzero
            have := congrFun hzero (0 : Fin (n + 1))
            simp [solve] at this
          · funext i
            exact Fin.elim0 i
  | succ m ih =>
      intro n h A
      cases n with
      | zero => omega
      | succ n =>
          by_cases hpivot : ∃ p : Fin (n + 1), A 0 p ≠ 0
          · let p := Fin.find (fun j ↦ A 0 j ≠ 0) hpivot
            let reduced := reduceAtPivot A p
            have hmn : m < n := by omega
            have hrec := ih n hmn reduced
            have hp : A 0 p ≠ 0 := Fin.find_spec hpivot
            rw [solve]
            simp only [hpivot, dite_true]
            constructor
            · exact liftAtPivot_ne_zero A p hrec.1
            · funext i
              refine Fin.cases ?_ (fun j ↦ ?_) i
              · exact firstRow_mulVec_liftAtPivot A p hp _
              · rw [tailRow_mulVec_liftAtPivot]
                exact congrFun hrec.2 j
          · let tail : Matrix (Fin m) (Fin (n + 1)) F :=
              fun i j ↦ A i.succ j
            have hmn : m < n + 1 := by omega
            have hrec := ih (n + 1) hmn tail
            rw [solve]
            simp only [hpivot, dite_false]
            constructor
            · exact hrec.1
            · funext i
              refine Fin.cases ?_ (fun j ↦ ?_) i
              · rw [Matrix.mulVec_apply, dotProduct]
                apply Finset.sum_eq_zero
                intro j _hj
                have hz : A 0 j = 0 := by
                  by_contra hj
                  exact hpivot ⟨j, hj⟩
                simp [hz]
              · change tail.mulVec (solve m (n + 1) hmn tail).result j = 0
                exact congrFun hrec.2 j

/-- Convenient projections of `solve_spec`. -/
theorem solve_result_ne_zero [Nontrivial F] [LawfulFieldInverse F]
    {m n : ℕ} (h : m < n)
    (A : Matrix (Fin m) (Fin n) F) :
    (solve m n h A).result ≠ 0 :=
  (solve_spec m n h A).1

theorem solve_result_mem_kernel [Nontrivial F] [LawfulFieldInverse F]
    {m n : ℕ} (h : m < n)
    (A : Matrix (Fin m) (Fin n) F) :
    A.mulVec (solve m n h A).result = 0 :=
  (solve_spec m n h A).2

/-- The recursive elimination uses at most `8 m n² + n` charged field
operations on an `m`-by-`n` homogeneous system.  The loose constant keeps the
bound stable under the two recursion branches and is more than sufficient for
the decoder's final `q`-power estimate. -/
theorem solve_operations_le :
    ∀ (m n : ℕ) (h : m < n) (A : Matrix (Fin m) (Fin n) F),
      (solve m n h A).operations ≤ 8 * m * n ^ 2 + n := by
  intro m
  induction m with
  | zero =>
      intro n h A
      cases n with
      | zero => omega
      | succ n => simp [solve]
  | succ m ih =>
      intro n h A
      cases n with
      | zero => omega
      | succ n =>
          by_cases hpivot : ∃ p : Fin (n + 1), A 0 p ≠ 0
          · let p := Fin.find (fun j ↦ A 0 j ≠ 0) hpivot
            let reduced := reduceAtPivot A p
            have hmn : m < n := by omega
            have hrec := ih n hmn reduced
            rw [solve]
            simp only [hpivot, dite_true]
            nlinarith [Nat.zero_le m, Nat.zero_le n]
          · let tail : Matrix (Fin m) (Fin (n + 1)) F :=
              fun i j ↦ A i.succ j
            have hmn : m < n + 1 := by omega
            have hrec := ih (n + 1) hmn tail
            rw [solve]
            simp only [hpivot, dite_false]
            nlinarith [Nat.zero_le m, Nat.zero_le n]

section ArbitraryFiniteIndices

variable {ρ κ : Type*} [Fintype ρ] [Fintype κ]

/-- Reindex a finite matrix by canonical `Fin` enumerations and run the
checked solver.  Enumeration and reindexing are control operations and hence
carry no field-operation charge in the model. -/
noncomputable def solveFintype (h : Fintype.card ρ < Fintype.card κ)
    (A : Matrix ρ κ F) : FieldCost (κ → F) :=
  let er := Fintype.equivFin ρ
  let ec := Fintype.equivFin κ
  let AFin : Matrix (Fin (Fintype.card ρ)) (Fin (Fintype.card κ)) F :=
    fun i j ↦ A (er.symm i) (ec.symm j)
  FieldCost.map (fun z j ↦ z (ec j))
    (solve (Fintype.card ρ) (Fintype.card κ) h AFin)

private theorem solveFintype_mulVec_eq
    (h : Fintype.card ρ < Fintype.card κ) (A : Matrix ρ κ F)
    (i : ρ) :
    A.mulVec (solveFintype h A).result i =
      Matrix.mulVec (fun r c ↦
        A ((Fintype.equivFin ρ).symm r)
          ((Fintype.equivFin κ).symm c))
        (solve (Fintype.card ρ) (Fintype.card κ) h
          (fun r c ↦
            A ((Fintype.equivFin ρ).symm r)
              ((Fintype.equivFin κ).symm c))).result
        (Fintype.equivFin ρ i) := by
  rw [Matrix.mulVec_apply, Matrix.mulVec_apply, dotProduct, dotProduct]
  exact Fintype.sum_equiv (Fintype.equivFin κ)
    (fun j ↦ A i j * (solveFintype h A).result j)
    (fun j ↦
      A ((Fintype.equivFin ρ).symm (Fintype.equivFin ρ i))
          ((Fintype.equivFin κ).symm j) *
        (solve (Fintype.card ρ) (Fintype.card κ) h
          (fun r c ↦
            A ((Fintype.equivFin ρ).symm r)
              ((Fintype.equivFin κ).symm c))).result j)
    (by intro j; simp [solveFintype])

theorem solveFintype_result_ne_zero [Nontrivial F] [LawfulFieldInverse F]
    (h : Fintype.card ρ < Fintype.card κ) (A : Matrix ρ κ F) :
    (solveFintype h A).result ≠ 0 := by
  let er := Fintype.equivFin ρ
  let ec := Fintype.equivFin κ
  let AFin : Matrix (Fin (Fintype.card ρ)) (Fin (Fintype.card κ)) F :=
    fun i j ↦ A (er.symm i) (ec.symm j)
  have hz := solve_result_ne_zero h AFin
  intro hzero
  apply hz
  funext j
  have := congrFun hzero (ec.symm j)
  simpa [solveFintype, er, ec, AFin] using this

theorem solveFintype_result_mem_kernel [Nontrivial F] [LawfulFieldInverse F]
    (h : Fintype.card ρ < Fintype.card κ) (A : Matrix ρ κ F) :
    A.mulVec (solveFintype h A).result = 0 := by
  funext i
  rw [solveFintype_mulVec_eq]
  exact congrFun (solve_result_mem_kernel h
    (fun r c ↦
      A ((Fintype.equivFin ρ).symm r)
        ((Fintype.equivFin κ).symm c))) (Fintype.equivFin ρ i)

theorem solveFintype_operations_le
    (h : Fintype.card ρ < Fintype.card κ) (A : Matrix ρ κ F) :
    (solveFintype h A).operations ≤
      8 * Fintype.card ρ * Fintype.card κ ^ 2 + Fintype.card κ := by
  exact solve_operations_le _ _ h
    (fun r c ↦
      A ((Fintype.equivFin ρ).symm r)
        ((Fintype.equivFin κ).symm c))

end ArbitraryFiniteIndices

end GaussianKernel

end RSListDecoding
