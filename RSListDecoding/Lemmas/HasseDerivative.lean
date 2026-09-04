import RSListDecoding.Defs.HasseDerivative

/-!
# Taylor identities for Hasse derivatives

This module proves the forward and backward Taylor identities labeled
`eq:forward` and `eq:backward` in the manuscript.  The bounded statements are
the literal degree-`< k` versions used there.  The `eval₂` statements allow
the identities to be instantiated in a larger coefficient ring, in particular
with a polynomial ring as the target so that the displacement remains formal.
-/

noncomputable section

open scoped BigOperators

namespace RSListDecoding

open Polynomial

variable {R S : Type*}

/-- Coefficient formula for the manuscript's Hasse-derivative convention. -/
theorem coeff_hasseDerivative [Semiring R] (P : Polynomial R) (ell n : ℕ) :
    (hasseDerivative ell P).coeff n =
      (Nat.choose (n + ell) ell : R) * P.coeff (n + ell) := by
  exact Polynomial.hasseDeriv_coeff ell P n

/-- Hasse derivatives commute with extension of scalars. -/
theorem hasseDerivative_map [Semiring R] [Semiring S] (f : R →+* S)
    (P : Polynomial R) (ell : ℕ) :
    hasseDerivative ell (P.map f) = (hasseDerivative ell P).map f := by
  ext n
  simp only [coeff_hasseDerivative, coeff_map, map_mul, map_natCast]

/-- Forward Taylor identity, with the canonical support bound. -/
theorem hasseTaylor_forward [CommSemiring R] (P : Polynomial R) (x t : R) :
    P.eval (x + t) =
      ∑ ell ∈ Finset.range (P.natDegree + 1),
        hasseDerivativeAt ell P x * t ^ ell := by
  rw [add_comm, ← Polynomial.taylor_eval x P t]
  rw [Polynomial.eval_eq_sum_range]
  simp only [Polynomial.natDegree_taylor, Polynomial.taylor_coeff, hasseDerivativeAt]

/-- `eq:forward`: forward Taylor expansion for a polynomial of degree `< k`. -/
theorem hasseTaylor_forward_of_natDegree_lt [CommSemiring R]
    (P : Polynomial R) {k : ℕ} (hP : P.natDegree < k) (x t : R) :
    P.eval (x + t) =
      ∑ ell ∈ Finset.range k, hasseDerivativeAt ell P x * t ^ ell := by
  rw [add_comm, ← Polynomial.taylor_eval x P t]
  rw [Polynomial.eval_eq_sum_range' (n := k)]
  · simp only [Polynomial.taylor_coeff, hasseDerivativeAt]
  · simpa only [Polynomial.natDegree_taylor] using hP

/-- Backward Taylor identity, with the canonical support bound. -/
theorem hasseTaylor_backward [CommRing R] (P : Polynomial R) (x t : R) :
    P.eval x =
      ∑ ell ∈ Finset.range (P.natDegree + 1),
        hasseDerivativeAt ell P (x + t) * (-t) ^ ell := by
  simpa only [add_neg_cancel_right] using hasseTaylor_forward P (x + t) (-t)

/-- `eq:backward`: backward Taylor expansion for a polynomial of degree `< k`. -/
theorem hasseTaylor_backward_of_natDegree_lt [CommRing R]
    (P : Polynomial R) {k : ℕ} (hP : P.natDegree < k) (x t : R) :
    P.eval x =
      ∑ ell ∈ Finset.range k,
        hasseDerivativeAt ell P (x + t) * (-t) ^ ell := by
  simpa only [add_neg_cancel_right] using
    hasseTaylor_forward_of_natDegree_lt P hP (x + t) (-t)

/-- Forward Taylor identity after applying a coefficient homomorphism.  Taking
`S = Polynomial R` makes `x` and `t` formal polynomial expressions. -/
theorem hasseTaylor_forward_eval₂ [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P : Polynomial R) {k : ℕ} (hP : P.natDegree < k)
    (x t : S) :
    P.eval₂ f (x + t) =
      ∑ ell ∈ Finset.range k,
        (hasseDerivative ell P).eval₂ f x * t ^ ell := by
  have hmap : (P.map f).natDegree < k :=
    (Polynomial.natDegree_map_le (p := P) (f := f)).trans_lt hP
  simpa only [Polynomial.eval_map, hasseDerivativeAt, hasseDerivative_map] using
    hasseTaylor_forward_of_natDegree_lt (P.map f) hmap x t

/-- Backward Taylor identity after applying a coefficient homomorphism. -/
theorem hasseTaylor_backward_eval₂ [CommRing R] [CommRing S]
    (f : R →+* S) (P : Polynomial R) {k : ℕ} (hP : P.natDegree < k)
    (x t : S) :
    P.eval₂ f x =
      ∑ ell ∈ Finset.range k,
        (hasseDerivative ell P).eval₂ f (x + t) * (-t) ^ ell := by
  have hmap : (P.map f).natDegree < k :=
    (Polynomial.natDegree_map_le (p := P) (f := f)).trans_lt hP
  simpa only [Polynomial.eval_map, hasseDerivativeAt, hasseDerivative_map] using
    hasseTaylor_backward_of_natDegree_lt (P.map f) hmap x t

end RSListDecoding
