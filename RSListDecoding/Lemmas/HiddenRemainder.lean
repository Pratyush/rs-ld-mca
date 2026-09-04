import RSListDecoding.Lemmas.HasseDerivative
import Mathlib.Order.Interval.Finset.Nat

/-!
# The hidden Taylor remainder

This module isolates the polynomial remainder used in the manuscript's local
interpolation constraints.  We retain the displacement as the formal
polynomial variable `X`.  The definition is a finite tail of the backward
Hasse--Taylor expansion, so it involves no polynomial division and works over
an arbitrary commutative ring.
-/

noncomputable section

open scoped BigOperators

namespace RSListDecoding

open Polynomial

variable {R : Type*} [CommRing R]

/-- The `j`-th correction in the rearranged backward Taylor expansion.

For `1 ≤ j`, this is
`(-1)^(j+1) * X^j * P^[j](alpha + X)`.  The factored form used in the
definition makes the common factor `X` explicit. -/
def hiddenTaylorCorrection (P : Polynomial R) (alpha : R) (j : ℕ) : Polynomial R :=
  X * ((hasseDerivative j P).comp (C alpha + X) * (-X) ^ (j - 1))

/-- The hidden remainder after retaining derivative orders `1, ..., d`.

The upper endpoint merely provides a finite support bound.  Taking its maximum
with `d + 1` makes the definition valid without a side condition on `d`; when
`d` is at least the degree of `P`, the defining interval is empty. -/
def hiddenTaylorRemainder (d : ℕ) (P : Polynomial R) (alpha : R) : Polynomial R :=
  ∑ j ∈ Finset.Ico (d + 1) (max (d + 1) (P.natDegree + 1)),
    (hasseDerivative j P).comp (C alpha + X) * (-X) ^ (j - 1)

/-- Once every possibly nonzero derivative has been retained, the hidden tail
is empty. -/
@[simp]
theorem hiddenTaylorRemainder_eq_zero_of_natDegree_le (d : ℕ) (P : Polynomial R)
    (alpha : R) (hP : P.natDegree ≤ d) :
    hiddenTaylorRemainder d P alpha = 0 := by
  rw [hiddenTaylorRemainder, max_eq_left (Nat.add_le_add_right hP 1)]
  simp

/-- The factored correction has exactly the alternating sign displayed in the
manuscript. -/
theorem hiddenTaylorCorrection_eq_signed (P : Polynomial R) (alpha : R) {j : ℕ}
    (hj : 1 ≤ j) :
    hiddenTaylorCorrection P alpha j =
      C ((-1 : R) ^ (j + 1)) * X ^ j *
        (hasseDerivative j P).comp (C alpha + X) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  simp only [hiddenTaylorCorrection, Nat.add_sub_cancel_left]
  rw [show (-X : Polynomial R) = (-1) * X by ring, mul_pow]
  simp only [map_pow, map_neg, map_one]
  simp only [Nat.add_comm 1 i]
  rw [show i + 1 + 1 = i + 2 by omega, pow_add, pow_succ]
  ring

/-- Exact hidden-remainder identity in factored form.  It is valid for every
`d`; no degree hypothesis and no assumption `d < k` are needed. -/
theorem hiddenTaylor_identity (d : ℕ) (P : Polynomial R) (alpha : R) :
    P.comp (C alpha + X) =
      C (P.eval alpha) +
        ∑ j ∈ Finset.Ico 1 (d + 1), hiddenTaylorCorrection P alpha j +
          X * hiddenTaylorRemainder d P alpha := by
  let N := max (d + 1) (P.natDegree + 1)
  have hdeg : P.natDegree < N :=
    (Nat.lt_succ_self P.natDegree).trans_le (le_max_right _ _)
  have hbackward :=
    hasseTaylor_backward_eval₂ (C : R →+* Polynomial R) P hdeg (C alpha) X
  have hN : 0 < N := by
    dsimp [N]
    exact (Nat.succ_pos P.natDegree).trans_le (le_max_right _ _)
  have hsplit0 : Finset.range N = {0} ∪ Finset.Ico 1 N := by
    rw [Finset.range_eq_Ico, Finset.singleton_union]
    simpa using (Finset.insert_Ico_add_one_left_eq_Ico hN).symm
  have hsplitd : Finset.Ico 1 N =
      Finset.Ico 1 (d + 1) ∪ Finset.Ico (d + 1) N := by
    have hdN : d + 1 ≤ N := by
      dsimp [N]
      exact le_max_left _ _
    simpa only [Nat.succ_eq_add_one] using
      (Finset.Ico_union_Ico_eq_Ico (Nat.succ_le_succ d.zero_le) hdN).symm
  have hdisjoint0 : Disjoint ({0} : Finset ℕ) (Finset.Ico 1 N) := by
    simp
  have hdisjointd :
      Disjoint (Finset.Ico 1 (d + 1)) (Finset.Ico (d + 1) N) :=
    Finset.Ico_disjoint_Ico_consecutive _ _ _
  rw [hsplit0, Finset.sum_union hdisjoint0] at hbackward
  rw [hsplitd, Finset.sum_union hdisjointd] at hbackward
  simp only [Finset.sum_singleton, hasseDerivative, Polynomial.hasseDeriv_zero',
    Polynomial.eval₂_at_apply, pow_zero, mul_one] at hbackward
  change C (P.eval alpha) =
    P.comp (C alpha + X) +
      ((∑ j ∈ Finset.Ico 1 (d + 1),
          (hasseDerivative j P).comp (C alpha + X) * (-X) ^ j) +
        ∑ j ∈ Finset.Ico (d + 1) N,
          (hasseDerivative j P).comp (C alpha + X) * (-X) ^ j) at hbackward
  have hcorrection (j : ℕ) (hj : 1 ≤ j) :
      hiddenTaylorCorrection P alpha j =
        -((hasseDerivative j P).comp (C alpha + X) * (-X) ^ j) := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
    simp only [hiddenTaylorCorrection, Nat.add_sub_cancel_left]
    ring
  have hfirst :
      (∑ j ∈ Finset.Ico 1 (d + 1), hiddenTaylorCorrection P alpha j) =
        -∑ j ∈ Finset.Ico 1 (d + 1),
          (hasseDerivative j P).comp (C alpha + X) * (-X) ^ j := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hcorrection j (Finset.mem_Ico.mp hj).1
  have htail :
      X * hiddenTaylorRemainder d P alpha =
        -∑ j ∈ Finset.Ico (d + 1) N,
          (hasseDerivative j P).comp (C alpha + X) * (-X) ^ j := by
    dsimp [N]
    rw [hiddenTaylorRemainder, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj1 : 1 ≤ j := (Nat.succ_le_succ d.zero_le).trans (Finset.mem_Ico.mp hj).1
    exact hcorrection j hj1
  rw [hfirst, htail]
  rw [hbackward]
  ring

/-- Exact identity with the alternating signs written explicitly. -/
theorem hiddenTaylor_identity_signed (d : ℕ) (P : Polynomial R) (alpha : R) :
    P.comp (C alpha + X) =
      C (P.eval alpha) +
        ∑ j ∈ Finset.Ico 1 (d + 1),
          C ((-1 : R) ^ (j + 1)) * X ^ j *
            (hasseDerivative j P).comp (C alpha + X) +
          X * hiddenTaylorRemainder d P alpha := by
  rw [hiddenTaylor_identity]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  exact hiddenTaylorCorrection_eq_signed P alpha (Finset.mem_Ico.mp hj).1

/-- The hidden remainder vanishes to order at least `d` at the formal origin. -/
theorem X_pow_dvd_hiddenTaylorRemainder (d : ℕ) (P : Polynomial R) (alpha : R) :
    X ^ d ∣ hiddenTaylorRemainder d P alpha := by
  rw [hiddenTaylorRemainder]
  apply Finset.dvd_sum
  intro j hj
  have hdj : d ≤ j - 1 := by
    have := (Finset.mem_Ico.mp hj).1
    omega
  exact dvd_mul_of_dvd_right
    (pow_dvd_pow_of_dvd_of_le (by exact ⟨-1, by ring⟩ : X ∣ (-X)) hdj) _

/-- The numerator in the paper's quotient definition is exactly `X` times
the division-free remainder above. -/
theorem hiddenTaylor_numerator_eq (d : ℕ) (P : Polynomial R) (alpha : R) :
    P.comp (C alpha + X) - C (P.eval alpha) -
        ∑ j ∈ Finset.Ico 1 (d + 1),
          C ((-1 : R) ^ (j + 1)) * X ^ j *
            (hasseDerivative j P).comp (C alpha + X) =
      X * hiddenTaylorRemainder d P alpha := by
  rw [hiddenTaylor_identity_signed]
  ring

end RSListDecoding
