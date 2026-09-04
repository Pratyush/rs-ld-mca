import RSListDecoding.Defs.InterpolationSpace
import RSListDecoding.Lemmas.Parameters
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Degree budgets for the global interpolation space

This module proves the support consequences of `eq:global-space`.  It does
not address the dimension of the space: only the coordinate-degree and
weighted-degree budgets, together with their consequence after differential
specialization, live here.
-/

noncomputable section

open scoped BigOperators

namespace RSListDecoding

open Polynomial

/-- Every individual jet exponent is bounded by the total jet degree. -/
theorem jetExponent_le_totalJetDegree {d : ℕ}
    (u : JetVariable d →₀ ℕ) (j : Fin (d + 1)) :
    u (some j) ≤ totalJetDegree u := by
  exact Finsupp.le_degree j u.some

/-- The Kopparty weight of a monomial is bounded by the coarser global
weight that assigns weight `D` to every jet variable. -/
theorem weight_jetWeight_le_x_add_totalJetDegree {d D : ℕ}
    (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (jetWeight (r := d) D) u ≤
      u none + D * totalJetDegree u := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_option]
  simp only [jetWeight, nsmul_eq_mul, mul_one]
  rw [totalJetDegree, Finsupp.degree_eq_sum]
  simp only [Finset.mul_sum]
  apply Nat.add_le_add_left
  exact Finset.sum_le_sum fun j _ => by
    simpa [mul_comm] using
      Nat.mul_le_mul_left (u (some j)) (Nat.sub_le D j.val)

/-- Membership in the global interpolation space imposes the advertised
coordinate-degree cap on every jet variable. -/
theorem degreeOf_jet_le_of_mem_interpolationSpace
    {q d m A K B W C : ℕ} {Q : DifferentialPolynomial q d}
    (hQ : Q ∈ interpolationSpace q d m A K B W C)
    (j : Fin (d + 1)) :
    Q.degreeOf (some j) ≤ B := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro u hu
  exact (jetExponent_le_totalJetDegree u j).trans
    ((mem_interpolationSpace_iff.mp hQ u hu).2.1)

/-- Membership in the global interpolation space imposes the Kopparty
weighted-degree cap.  Positivity is necessary for the zero polynomial when
the target bound is strict. -/
theorem weightedTotalDegree_lt_of_mem_interpolationSpace
    {q d m A K B W C : ℕ} {Q : DifferentialPolynomial q d}
    (hbudget : 0 < m * A)
    (hQ : Q ∈ interpolationSpace q d m A K B W C) :
    Q.weightedTotalDegree (jetWeight (r := d) (K - 1)) < m * A := by
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_lt_iff hbudget]
  intro u hu
  exact (weight_jetWeight_le_x_add_totalJetDegree u).trans_lt
    ((mem_interpolationSpace_iff.mp hQ u hu).2.2.1)

/-- The polynomial substituted for a differential variable has degree at
most its Kopparty weight. -/
theorem natDegree_specializationVariable_le {q r D : ℕ}
    (P : Polynomial (ZMod q)) (hP : P.natDegree ≤ D)
    (v : JetVariable r) :
    (match v with
      | none => Polynomial.X
      | some j => hasseDerivative (j : ℕ) P).natDegree ≤
      jetWeight D v := by
  cases v with
  | none => exact Polynomial.natDegree_X_le
  | some j =>
      exact (Polynomial.natDegree_hasseDeriv_le P j.val).trans
        (Nat.sub_le_sub_right hP j.val)

/-- Differential specialization cannot increase degree past the Kopparty
weighted total degree. -/
theorem natDegree_differentialSpecialization_le_weightedTotalDegree
    {q r D : ℕ} (Q : DifferentialPolynomial q r)
    (P : Polynomial (ZMod q)) (hP : P.natDegree ≤ D) :
    (differentialSpecialization Q P).natDegree ≤
      Q.weightedTotalDegree (jetWeight (r := r) D) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum Q]
  simp only [differentialSpecialization, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro u hu
  rw [MvPolynomial.eval₂Hom_monomial]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le u.support
    (fun v => (match v with
      | none => Polynomial.X
      | some j => hasseDerivative (j : ℕ) P) ^ u v)).trans ?_
  calc
    ∑ v ∈ u.support,
        ((match v with
          | none => Polynomial.X
          | some j => hasseDerivative (j : ℕ) P) ^ u v).natDegree
        ≤ ∑ v ∈ u.support, u v * jetWeight D v := by
          apply Finset.sum_le_sum
          intro v hv
          exact Polynomial.natDegree_pow_le.trans
            (Nat.mul_le_mul_left (u v)
              (natDegree_specializationVariable_le P hP v))
    _ = Finsupp.weight (jetWeight (r := r) D) u := by
          rw [Finsupp.weight_apply]
          simp only [Finsupp.sum, nsmul_eq_mul, Nat.cast_id]
    _ ≤ Q.weightedTotalDegree (jetWeight (r := r) D) :=
          MvPolynomial.le_weightedTotalDegree _ hu

/-- The global support budget gives the strict univariate degree bound used
in the multiplicity-root argument. -/
theorem natDegree_differentialSpecialization_lt_of_mem_interpolationSpace
    {q d m A K B W C : ℕ} {Q : DifferentialPolynomial q d}
    (hbudget : 0 < m * A)
    (hQ : Q ∈ interpolationSpace q d m A K B W C)
    (P : Polynomial (ZMod q)) (hP : P.natDegree ≤ K - 1) :
    (differentialSpecialization Q P).natDegree < m * A :=
  (natDegree_differentialSpecialization_le_weightedTotalDegree Q P hP).trans_lt
    (weightedTotalDegree_lt_of_mem_interpolationSpace hbudget hQ)

/-! ## Wrappers for the rounded parameters in the capstone -/

/-- Coordinate-degree budget with `d,m,A,K,B` instantiated by the rounded
parameters of the combinatorial theorem. -/
theorem scoped_degreeOf_jet_le_of_mem_interpolationSpace
    {q n W C : ℕ} {ε θ : ℝ}
    {Q : DifferentialPolynomial q (derivativeOrder ε θ)}
    (hQ : Q ∈ interpolationSpace q (derivativeOrder ε θ)
      (multiplicity ε θ) (agreementThreshold ε n)
      (ambientDimension ε θ n) (interpolationDegreeBudget ε θ n) W C)
    (j : Fin (derivativeOrder ε θ + 1)) :
    Q.degreeOf (some j) ≤ interpolationDegreeBudget ε θ n :=
  degreeOf_jet_le_of_mem_interpolationSpace hQ j

/-- Weighted-degree budget with the rounded capstone parameters. -/
theorem scoped_weightedTotalDegree_lt_of_mem_interpolationSpace
    {q n W C : ℕ} {ε θ : ℝ}
    (hε : 0 < ε) (hn : 0 < n)
    {Q : DifferentialPolynomial q (derivativeOrder ε θ)}
    (hQ : Q ∈ interpolationSpace q (derivativeOrder ε θ)
      (multiplicity ε θ) (agreementThreshold ε n)
      (ambientDimension ε θ n) (interpolationDegreeBudget ε θ n) W C) :
    Q.weightedTotalDegree
        (jetWeight (r := derivativeOrder ε θ) (ambientDimension ε θ n - 1)) <
      multiplicity ε θ * agreementThreshold ε n := by
  apply weightedTotalDegree_lt_of_mem_interpolationSpace _ hQ
  exact Nat.mul_pos (multiplicity_pos θ hε) (agreementThreshold_pos hε hn)

/-- Univariate specialization budget with all global parameters instantiated
as in the capstone. -/
theorem scoped_natDegree_differentialSpecialization_lt_of_mem_interpolationSpace
    {q n W C : ℕ} {ε θ : ℝ}
    (hε : 0 < ε) (hn : 0 < n)
    {Q : DifferentialPolynomial q (derivativeOrder ε θ)}
    (hQ : Q ∈ interpolationSpace q (derivativeOrder ε θ)
      (multiplicity ε θ) (agreementThreshold ε n)
      (ambientDimension ε θ n) (interpolationDegreeBudget ε θ n) W C)
    (P : Polynomial (ZMod q))
    (hP : P.natDegree ≤ ambientDimension ε θ n - 1) :
    (differentialSpecialization Q P).natDegree <
      multiplicity ε θ * agreementThreshold ε n := by
  exact natDegree_differentialSpecialization_lt_of_mem_interpolationSpace
    (Nat.mul_pos (multiplicity_pos θ hε) (agreementThreshold_pos hε hn)) hQ P hP

end RSListDecoding
