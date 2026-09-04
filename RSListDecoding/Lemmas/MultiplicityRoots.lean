import Mathlib.Algebra.Polynomial.Roots

/-!
# A degree bound for roots of uniform multiplicity

This module packages the elementary fact used by the contact argument: a
polynomial whose degree is smaller than the total multiplicity of a family of
distinct prescribed roots must vanish.
-/

open scoped BigOperators

namespace RSListDecoding

open Polynomial

/-- If `p` is divisible by the `m`th power of the linear factor at every
point indexed by `S`, and these points are distinct, then a degree strictly
below `m * S.card` forces `p` to be zero.

The statement deliberately permits `m = 0` and `S = ∅`: in either case its
strict degree hypothesis is impossible, so no extra positivity assumption is
needed. -/
theorem eq_zero_of_natDegree_lt_card_mul_of_pow_X_sub_C_dvd
    {F : Type*} [Field F] {n m : ℕ} (alpha : Fin n → F)
    (halpha : Function.Injective alpha) (S : Finset (Fin n)) (p : F[X])
    (hdiv : ∀ i ∈ S, (X - C (alpha i)) ^ m ∣ p)
    (hdeg : p.natDegree < m * S.card) :
    p = 0 := by
  have hpairwise :
      (S : Set (Fin n)).Pairwise
        (fun i j ↦ IsCoprime ((X - C (alpha i)) ^ m)
          ((X - C (alpha j)) ^ m)) := by
    intro i _hi j _hj hij
    exact (pairwise_coprime_X_sub_C halpha hij).pow
  have hproductDivides :
      (∏ i ∈ S, (X - C (alpha i)) ^ m) ∣ p :=
    Finset.prod_dvd_of_coprime hpairwise hdiv
  apply eq_zero_of_dvd_of_natDegree_lt hproductDivides
  rw [natDegree_prod_of_monic]
  · simpa [natDegree_pow, Nat.mul_comm] using hdeg
  · intro i _hi
    exact (monic_X_sub_C (alpha i)).pow m

/-- Agreement-set specialization of
`eq_zero_of_natDegree_lt_card_mul_of_pow_X_sub_C_dvd`: it is enough that the
set contain at least `A` indices and that `p.natDegree < m * A`. -/
theorem eq_zero_of_natDegree_lt_agreement_mul_of_pow_X_sub_C_dvd
    {F : Type*} [Field F] {n m A : ℕ} (alpha : Fin n → F)
    (halpha : Function.Injective alpha) (S : Finset (Fin n)) (p : F[X])
    (hcard : A ≤ S.card)
    (hdiv : ∀ i ∈ S, (X - C (alpha i)) ^ m ∣ p)
    (hdeg : p.natDegree < m * A) :
    p = 0 := by
  apply eq_zero_of_natDegree_lt_card_mul_of_pow_X_sub_C_dvd
      alpha halpha S p hdiv
  exact hdeg.trans_le (Nat.mul_le_mul_left m hcard)

end RSListDecoding
