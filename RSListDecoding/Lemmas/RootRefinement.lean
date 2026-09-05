import RSListDecoding.Defs.DifferentialEquation
import RSListDecoding.Lemmas.HasseDerivative
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The degree-below-characteristic root refinement

This file contains the algebraic ingredients of the refined root count.  In
particular, finite extension fields are Mathlib's `GaloisField`; no field
construction or field-cardinality fact is assumed by this project.
-/

noncomputable section

open scoped BigOperators

namespace RSListDecoding

open MvPolynomial Polynomial

/-- The extension field used to expose a regular evaluation point. -/
abbrev RootExtension (q e : ℕ) [Fact q.Prime] := GaloisField q e

section GaloisField

variable {q e : ℕ} [Fact q.Prime]

/-- Mathlib's degree-`e` Galois field has the expected cardinality. -/
theorem rootExtension_natCard (he : e ≠ 0) :
    Nat.card (RootExtension q e) = q ^ e := by
  exact GaloisField.card q e he

/-- Fintype-facing form of the Galois-field cardinality, suitable for the
finite evaluator and the refinement-key count. -/
theorem rootExtension_fintypeCard (he : e ≠ 0) :
    letI : Fintype (RootExtension q e) := Fintype.ofFinite _
    Fintype.card (RootExtension q e) = q ^ e := by
  letI : Fintype (RootExtension q e) := Fintype.ofFinite _
  rw [← Nat.card_eq_fintype_card]
  exact rootExtension_natCard he

/-- The prime field embeds in Mathlib's Galois field. -/
theorem rootExtension_algebraMap_injective :
    Function.Injective (algebraMap (ZMod q) (RootExtension q e)) := by
  exact FaithfulSMul.algebraMap_injective _ _

/-- Hasse differentiation commutes with passage to the Galois field. -/
theorem hasseDerivative_map_rootExtension (j : ℕ) (P : Polynomial (ZMod q)) :
    hasseDerivative j (P.map (algebraMap (ZMod q) (RootExtension q e))) =
      (hasseDerivative j P).map (algebraMap (ZMod q) (RootExtension q e)) := by
  exact hasseDerivative_map (algebraMap (ZMod q) (RootExtension q e)) P j

end GaloisField

section ScalarExtension

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {r : ℕ}

set_option maxHeartbeats 400000 in
/-- Differential specialization commutes with scalar extension. -/
theorem differentialSpecializationOver_map (f : R →+* S)
    (Q : DifferentialPolynomialOver R r) (P : Polynomial R) :
    (differentialSpecializationOver Q P).map f =
      differentialSpecializationOver (MvPolynomial.map f Q) (P.map f) := by
  rw [differentialSpecializationOver, differentialSpecializationOver]
  change Polynomial.mapRingHom f
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun v : JetVariable r => match v with
          | none => Polynomial.X
          | some j => hasseDerivative (j : ℕ) P) Q) = _
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.eval₂Hom_map_hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext x
    simp [Polynomial.coe_mapRingHom]
  · funext v
    rcases v with (_ | j)
    · simp
    · simp only [Polynomial.coe_mapRingHom, hasseDerivative_map]
  · rfl

/-- In particular, a solution over the prime field remains a solution after
embedding it into a field extension. -/
theorem differentialSpecializationOver_map_eq_zero (f : R →+* S)
    (Q : DifferentialPolynomialOver R r) (P : Polynomial R)
    (h : differentialSpecializationOver Q P = 0) :
    differentialSpecializationOver (MvPolynomial.map f Q) (P.map f) = 0 := by
  rw [← differentialSpecializationOver_map f Q P, h, Polynomial.map_zero]

/-- Scalar extension on degree-bounded polynomials. -/
def mapDegreeLT (f : R →+* S) (n : ℕ) :
    Polynomial.degreeLT R n → Polynomial.degreeLT S n := fun P =>
  ⟨P.1.map f, Polynomial.mem_degreeLT.2 <|
    (Polynomial.degree_map_le.trans_lt (Polynomial.mem_degreeLT.1 P.2))⟩

/-- An injective scalar map remains injective on degree-bounded
polynomials. -/
theorem mapDegreeLT_injective (f : R →+* S) (hf : Function.Injective f)
    (n : ℕ) : Function.Injective (mapDegreeLT f n) := by
  intro P P' h
  apply Subtype.ext
  exact Polynomial.map_injective f hf (Subtype.ext_iff.mp h)

variable [Fintype R] [Fintype S]

@[simp]
theorem mem_differentialSolutionsOver {D : ℕ}
    (Q : DifferentialPolynomialOver R r) (P : Polynomial.degreeLT R (D + 1)) :
    P ∈ differentialSolutionsOver D Q ↔
      differentialSpecializationOver Q P = 0 := by
  classical
  simp [differentialSolutionsOver]

/-- Scalar extension maps the exact finite evaluator's output into the
extension-field output. -/
theorem mapDegreeLT_mem_differentialSolutionsOver (f : R →+* S)
    {D : ℕ} (Q : DifferentialPolynomialOver R r)
    (P : Polynomial.degreeLT R (D + 1))
    (hP : P ∈ differentialSolutionsOver D Q) :
    mapDegreeLT f (D + 1) P ∈
      differentialSolutionsOver D (MvPolynomial.map f Q) := by
  rw [mem_differentialSolutionsOver] at hP ⊢
  exact differentialSpecializationOver_map_eq_zero f Q P hP

/-- Passing to an extension field cannot decrease the number of solutions. -/
theorem card_differentialSolutionsOver_le_map (f : R →+* S)
    (hf : Function.Injective f) {D : ℕ}
    (Q : DifferentialPolynomialOver R r) :
    (differentialSolutionsOver D Q).card ≤
      (differentialSolutionsOver D (MvPolynomial.map f Q)).card := by
  classical
  apply Finset.card_le_card_of_injOn (mapDegreeLT f (D + 1))
  · intro P hP
    exact mapDegreeLT_mem_differentialSolutionsOver f Q P hP
  · exact (mapDegreeLT_injective f hf (D + 1)).injOn

/-- Injective scalar extension preserves each coordinate degree. -/
theorem degreeOf_map_of_injective (f : R →+* S)
    (hf : Function.Injective f) (Q : DifferentialPolynomialOver R r)
    (v : JetVariable r) :
    (MvPolynomial.map f Q).degreeOf v = Q.degreeOf v := by
  classical
  simp only [MvPolynomial.degreeOf_eq_sup,
    MvPolynomial.support_map_of_injective Q hf]

/-- Injective scalar extension preserves weighted total degree. -/
theorem weightedTotalDegree_map_of_injective (f : R →+* S)
    (hf : Function.Injective f) (Q : DifferentialPolynomialOver R r)
    (w : JetVariable r → ℕ) :
    (MvPolynomial.map f Q).weightedTotalDegree w =
      Q.weightedTotalDegree w := by
  classical
  simp only [MvPolynomial.weightedTotalDegree,
    MvPolynomial.support_map_of_injective Q hf]

/-- Injective scalar extension preserves nonzeroness. -/
theorem mvPolynomial_map_ne_zero (f : R →+* S)
    (hf : Function.Injective f) {Q : DifferentialPolynomialOver R r}
    (hQ : Q ≠ 0) : MvPolynomial.map f Q ≠ 0 := by
  exact fun h => hQ (MvPolynomial.map_injective f hf (by simpa using h))

end ScalarExtension

section Binomial

variable {F : Type*} [Field F] {q D i j : ℕ} [CharP F q]

/-- In characteristic `q`, every binomial coefficient occurring in a lift of
degree at most `D < q` is nonzero.  This is the precise algebraic reason that
the generic Hensel branching factor becomes one. -/
theorem natCast_choose_ne_zero_of_lt_char
    (hq : q.Prime) (hij : j ≤ i) (hiD : i ≤ D) (hDq : D < q) :
    (i.choose j : F) ≠ 0 := by
  intro hzero
  have hdvd : q ∣ i.choose j :=
    (CharP.cast_eq_zero_iff F q (i.choose j)).mp hzero
  exact (hq.coprime_iff_not_dvd.mp
    (Nat.Prime.coprime_choose_of_lt hq (hiD.trans_lt hDq) hij)) hdvd

end Binomial

section PartialHasse

variable {R σ : Type*} [CommSemiring R] [DecidableEq σ]

/-- Regard a multivariate polynomial as a univariate polynomial in `x`, with
coefficients in the polynomial ring on all other variables. -/
def isolateVariableEquiv (x : σ) :
    MvPolynomial σ R ≃ₐ[R] Polynomial (MvPolynomial {y : σ // y ≠ x} R) :=
  (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe x).symm).trans
    (MvPolynomial.optionEquivLeft R {y : σ // y ≠ x})

@[simp]
theorem isolateVariableEquiv_X_self (x : σ) :
    isolateVariableEquiv x (MvPolynomial.X x : MvPolynomial σ R) =
      Polynomial.X := by
  simp [isolateVariableEquiv, MvPolynomial.renameEquiv_apply]

@[simp]
theorem isolateVariableEquiv_X_ne {x y : σ} (h : y ≠ x) :
    isolateVariableEquiv x (MvPolynomial.X y : MvPolynomial σ R) =
      Polynomial.C (MvPolynomial.X ⟨y, h⟩) := by
  simp [isolateVariableEquiv, MvPolynomial.renameEquiv_apply, h]

/-- Under the univariate presentation, partial differentiation is ordinary
polynomial differentiation. -/
theorem isolateVariableEquiv_pderiv (x : σ) (Q : MvPolynomial σ R) :
    isolateVariableEquiv x (MvPolynomial.pderiv x Q) =
      Polynomial.derivative (isolateVariableEquiv x Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [isolateVariableEquiv]
  | add p q hp hq => simp [hp, hq]
  | mul_X p y hp =>
      rw [MvPolynomial.pderiv_mul]
      simp only [map_add, map_mul, hp, Polynomial.derivative_mul]
      by_cases h : y = x
      · subst y
        simp
      · simp [h, isolateVariableEquiv_X_ne h]

/-- The Hasse partial derivative in a single multivariate coordinate.  Unlike
an iterated ordinary derivative, the top derivative cannot disappear in
small characteristic. -/
def partialHasse (x : σ) (m : ℕ) (Q : MvPolynomial σ R) :
    MvPolynomial σ R :=
  (isolateVariableEquiv x).symm
    (Polynomial.hasseDeriv m (isolateVariableEquiv x Q))

@[simp]
theorem isolateVariableEquiv_partialHasse
    (x : σ) (m : ℕ) (Q : MvPolynomial σ R) :
    isolateVariableEquiv x (partialHasse x m Q) =
      Polynomial.hasseDeriv m (isolateVariableEquiv x Q) := by
  simp [partialHasse]

@[simp]
theorem partialHasse_zero (x : σ) (Q : MvPolynomial σ R) :
    partialHasse x 0 Q = Q := by
  apply (isolateVariableEquiv x).injective
  simp

/-- The separant of an order-`m` Hasse stratum is the next stratum, scaled
by `m+1`. -/
theorem pderiv_partialHasse (x : σ) (m : ℕ) (Q : MvPolynomial σ R) :
    MvPolynomial.pderiv x (partialHasse x m Q) =
      (m + 1) • partialHasse x (m + 1) Q := by
  apply (isolateVariableEquiv x).injective
  rw [isolateVariableEquiv_pderiv]
  simp only [isolateVariableEquiv_partialHasse, map_nsmul]
  have h := LinearMap.congr_fun
    (Polynomial.hasseDeriv_comp
      (R := MvPolynomial {y : σ // y ≠ x} R) 1 m)
    (isolateVariableEquiv x Q)
  simpa [Polynomial.hasseDeriv_one, Nat.choose_one_right, Nat.add_comm,
    add_smul] using h

/-- Taking an `m`-th Hasse partial derivative lowers the active coordinate
degree by at least `m`. -/
theorem partialHasse_degreeOf (x : σ) (m : ℕ) (Q : MvPolynomial σ R) :
    (partialHasse x m Q).degreeOf x ≤ Q.degreeOf x - m := by
  rw [MvPolynomial.degreeOf_eq_natDegree x,
    MvPolynomial.degreeOf_eq_natDegree x]
  change (isolateVariableEquiv x (partialHasse x m Q)).natDegree ≤
    (isolateVariableEquiv x Q).natDegree - m
  rw [isolateVariableEquiv_partialHasse]
  exact Polynomial.natDegree_hasseDeriv_le _ _

/-- The top Hasse partial derivative of a nonzero polynomial is nonzero. -/
theorem partialHasse_top_ne_zero [NoZeroDivisors R] [Nontrivial R]
    (x : σ) (Q : MvPolynomial σ R) (hQ : Q ≠ 0) :
    partialHasse x (Q.degreeOf x) Q ≠ 0 := by
  intro hz
  have hz' := congrArg (isolateVariableEquiv x) hz
  simp only [isolateVariableEquiv_partialHasse, map_zero] at hz'
  rw [MvPolynomial.degreeOf_eq_natDegree x] at hz'
  change Polynomial.hasseDeriv (isolateVariableEquiv x Q).natDegree
    (isolateVariableEquiv x Q) = 0 at hz'
  rw [Polynomial.hasseDeriv_natDegree_eq_C] at hz'
  have hlead : (isolateVariableEquiv x Q).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr
      ((isolateVariableEquiv x).injective.ne hQ)
  apply hlead
  apply Polynomial.C_injective
  simpa using hz'

/-- Before the characteristic, a nonzero next Hasse stratum gives a nonzero
ordinary separant for the current stratum. -/
theorem pderiv_partialHasse_ne_zero_of_next
    {F : Type*} [Field F] {q m : ℕ} [CharP F q]
    (hmq : m + 1 < q) (x : σ) (Q : MvPolynomial σ F)
    (hnext : partialHasse x (m + 1) Q ≠ 0) :
    MvPolynomial.pderiv x (partialHasse x m Q) ≠ 0 := by
  rw [pderiv_partialHasse, nsmul_eq_mul]
  apply mul_ne_zero
  · change ((m + 1 : ℕ) : MvPolynomial σ F) ≠ 0
    rw [show ((m + 1 : ℕ) : MvPolynomial σ F) =
      MvPolynomial.C ((m + 1 : ℕ) : F) by simp]
    exact MvPolynomial.C_ne_zero.mpr
      ((CharP.cast_eq_zero_iff F q (m + 1)).not.mpr
        (Nat.not_dvd_of_pos_of_lt (by omega) hmq))
  · exact hnext

/-- Explicit monomial formula for a Hasse partial derivative. -/
theorem partialHasse_monomial
    (x : σ) (m : ℕ) (u : σ →₀ ℕ) (a : R) :
    partialHasse x m (MvPolynomial.monomial u a) =
      MvPolynomial.monomial (u - Finsupp.single x m)
        ((u x).choose m * a) := by
  apply (isolateVariableEquiv x).injective
  simp [partialHasse, isolateVariableEquiv,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_monomial,
    MvPolynomial.optionEquivLeft_monomial, Polynomial.hasseDeriv_monomial]
  have hexp :
      (Finsupp.mapDomain (Equiv.optionSubtypeNe x).symm
        (u - Finsupp.single x m)).some =
      (Finsupp.mapDomain (Equiv.optionSubtypeNe x).symm u).some := by
    ext y
    rw [Finsupp.some_apply, Finsupp.some_apply,
      Finsupp.mapDomain_equiv_apply, Finsupp.mapDomain_equiv_apply]
    change u y - Finsupp.single x m y = u y
    rw [Finsupp.single_eq_of_ne y.property]
    simp
  rw [hexp]
  congr 1
  change MvPolynomial.C ((u x).choose m : R) *
      MvPolynomial.monomial _ a = _
  rw [MvPolynomial.C_mul_monomial]

theorem partialHasse_add (x : σ) (m : ℕ) (Q Q' : MvPolynomial σ R) :
    partialHasse x m (Q + Q') = partialHasse x m Q + partialHasse x m Q' := by
  apply (isolateVariableEquiv x).injective
  simp

theorem partialHasse_finset_sum
    {ι : Type*} (x : σ) (m : ℕ) (s : Finset ι)
    (f : ι → MvPolynomial σ R) :
    partialHasse x m (∑ i ∈ s, f i) =
      ∑ i ∈ s, partialHasse x m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [partialHasse]
  | @insert a s ha ih => simp [ha, ih, partialHasse_add]

/-- Expansion of a Hasse partial derivative over the original support. -/
theorem partialHasse_as_sum (x : σ) (m : ℕ) (Q : MvPolynomial σ R) :
    partialHasse x m Q =
      ∑ u ∈ Q.support, MvPolynomial.monomial
        (u - Finsupp.single x m) ((u x).choose m * Q.coeff u) := by
  conv_lhs => rw [MvPolynomial.as_sum Q]
  rw [partialHasse_finset_sum]
  apply Finset.sum_congr rfl
  intro u _hu
  exact partialHasse_monomial x m u (Q.coeff u)

/-- Removing multiplicity from one coordinate cannot increase a nonnegative
monomial weight. -/
theorem finsupp_weight_tsub_single_le
    (w : σ → ℕ) (u : σ →₀ ℕ) (x : σ) (m : ℕ) :
    Finsupp.weight w (u - Finsupp.single x m) ≤ Finsupp.weight w u := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  apply Finsupp.sum_le_sum_index (tsub_le_self)
  · intro i _hi a b hab
    exact Nat.mul_le_mul_right (w i) hab
  · intro _i _hi
    simp

/-- Hasse partial differentiation preserves the weighted-degree budget. -/
theorem weightedTotalDegree_partialHasse_le
    (w : σ → ℕ) (x : σ) (m : ℕ) (Q : MvPolynomial σ R) :
    (partialHasse x m Q).weightedTotalDegree w ≤
      Q.weightedTotalDegree w := by
  classical
  rw [partialHasse_as_sum]
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  intro v hv
  have hv' := MvPolynomial.support_sum hv
  obtain ⟨u, hu, hvmono⟩ := Finset.mem_biUnion.mp hv'
  have hv_eq : v = u - Finsupp.single x m := by
    by_cases hc : ((u x).choose m : R) * Q.coeff u = 0
    · simp [hc] at hvmono
    · simpa [MvPolynomial.support_monomial, hc] using hvmono
  subst v
  exact (finsupp_weight_tsub_single_le w u x m).trans
    (MvPolynomial.le_weightedTotalDegree w hu)

/-- Hasse partial differentiation cannot introduce a variable that was not
already present. -/
theorem partialHasse_vars_subset
    (x : σ) (m : ℕ) (Q : MvPolynomial σ R) :
    (partialHasse x m Q).vars ⊆ Q.vars := by
  classical
  intro y hy
  rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hy ⊢
  intro hyzero
  have hle := weightedTotalDegree_partialHasse_le
    (Pi.single y 1) x m Q
  rw [MvPolynomial.weightedTotalDegree_piSingle,
    MvPolynomial.weightedTotalDegree_piSingle, hyzero] at hle
  exact hy (Nat.eq_zero_of_le_zero hle)

/-- Hasse differentiation in one coordinate cannot increase the degree in
any coordinate. -/
theorem partialHasse_degreeOf_le
    (x : σ) (m : ℕ) (Q : MvPolynomial σ R) (y : σ) :
    (partialHasse x m Q).degreeOf y ≤ Q.degreeOf y := by
  have hle := weightedTotalDegree_partialHasse_le (Pi.single y 1) x m Q
  simpa only [MvPolynomial.weightedTotalDegree_piSingle] using hle

/-- A sequence starting at zero and ending nonzero has a first transition
from a zero value to a nonzero value. -/
theorem exists_zero_succ_ne_zero
    {α : Type*} [Zero α] (f : ℕ → α) {d : ℕ}
    (hzero : f 0 = 0) (htop : f d ≠ 0) :
    ∃ m < d, f m = 0 ∧ f (m + 1) ≠ 0 := by
  induction d with
  | zero => exact (htop hzero).elim
  | succ d ih =>
      by_cases hd : f d = 0
      · exact ⟨d, Nat.lt_succ_self d, hd, by simpa using htop⟩
      · obtain ⟨m, hm, hm0, hm1⟩ := ih hd
        exact ⟨m, hm.trans (Nat.lt_succ_self d), hm0, hm1⟩

/-- If the next specialized Hasse stratum is nonzero, then the specialized
ordinary separant of the current stratum is nonzero before the
characteristic. -/
theorem differentialSpecializationOver_pderiv_partialHasse_ne_zero
    {F : Type*} [Field F] {r q m : ℕ} [CharP F q]
    (hmq : m + 1 < q) (x : JetVariable r)
    (Q : DifferentialPolynomialOver F r) (P : Polynomial F)
    (hnext : differentialSpecializationOver
      (partialHasse x (m + 1) Q) P ≠ 0) :
    differentialSpecializationOver
      (MvPolynomial.pderiv x (partialHasse x m Q)) P ≠ 0 := by
  rw [pderiv_partialHasse]
  change MvPolynomial.eval₂Hom Polynomial.C _ ((m + 1) •
    partialHasse x (m + 1) Q) ≠ 0
  rw [map_nsmul, nsmul_eq_mul]
  apply mul_ne_zero
  · change ((m + 1 : ℕ) : Polynomial F) ≠ 0
    rw [show ((m + 1 : ℕ) : Polynomial F) =
      Polynomial.C ((m + 1 : ℕ) : F) by simp]
    exact Polynomial.C_ne_zero.mpr
      ((CharP.cast_eq_zero_iff F q (m + 1)).not.mpr
        (Nat.not_dvd_of_pos_of_lt (by omega) hmq))
  · exact hnext

/-- The top Hasse partial derivative eliminates its active variable. -/
theorem partialHasse_top_notMem_vars
    [NoZeroDivisors R] [Nontrivial R]
    (x : σ) (Q : MvPolynomial σ R) :
    x ∉ (partialHasse x (Q.degreeOf x) Q).vars := by
  rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero, not_ne_iff]
  exact Nat.eq_zero_of_le_zero
    ((partialHasse_degreeOf x (Q.degreeOf x) Q).trans (by simp))

end PartialHasse

section DifferentialJet

variable {F : Type*} [Field F]

/-- Hasse differentiation commutes with translation. -/
theorem hasseDerivative_taylor_comm
    (j : ℕ) (a : F) (P : Polynomial F) :
    hasseDerivative j (Polynomial.taylor a P) =
      Polynomial.taylor a (hasseDerivative j P) := by
  ext n
  rw [Polynomial.hasseDeriv_coeff, Polynomial.taylor_coeff,
    Polynomial.taylor_coeff]
  have hcomp := LinearMap.congr_fun
    (Polynomial.hasseDeriv_comp (R := F) n j) P
  simp only [LinearMap.comp_apply] at hcomp
  rw [hcomp, LinearMap.smul_apply, Polynomial.eval_smul, nsmul_eq_mul]
  rw [Nat.choose_symm_add]

/-- The differential jet of `P` at an arbitrary expansion point. -/
def differentialJet {r : ℕ} (a : F) (P : Polynomial F) : JetVariable r → F
  | none => a
  | some i => (hasseDerivative (i : ℕ) P).eval a

/-- Evaluating a differential specialization at `a` is the same as
evaluating the original multivariate polynomial on the differential jet at
`a`. -/
theorem eval_differentialSpecializationOver {r : ℕ}
    (Q : DifferentialPolynomialOver F r) (P : Polynomial F) (a : F) :
    (differentialSpecializationOver Q P).eval a =
      MvPolynomial.eval (differentialJet a P) Q := by
  rw [differentialSpecializationOver]
  change Polynomial.evalRingHom a
    (MvPolynomial.eval₂Hom Polynomial.C
      (fun v : JetVariable r => match v with
        | none => Polynomial.X
        | some i => hasseDerivative (i : ℕ) P) Q) = _
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext c
    simp
  · funext v
    rcases v with (_ | i)
    · simp [differentialJet]
    · simp [differentialJet]
  · rfl

/-- Translate the independent variable of a differential equation by `a`,
leaving all jet variables fixed. -/
def translateDifferential {r : ℕ} (a : F)
    (Q : DifferentialPolynomialOver F r) : DifferentialPolynomialOver F r :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v : JetVariable r => match v with
      | none => MvPolynomial.X none + MvPolynomial.C a
      | some i => MvPolynomial.X (some i)) Q

/-- Differential specialization commutes with simultaneous translation of
the independent variable and candidate polynomial. -/
theorem differentialSpecializationOver_translate {r : ℕ} (a : F)
    (Q : DifferentialPolynomialOver F r) (P : Polynomial F) :
    differentialSpecializationOver (translateDifferential a Q)
        (Polynomial.taylor a P) =
      Polynomial.taylor a (differentialSpecializationOver Q P) := by
  let subst : JetVariable r → Polynomial F := fun v => match v with
    | none => Polynomial.X
    | some i => hasseDerivative (i : ℕ) P
  let substTaylor : JetVariable r → Polynomial F := fun v => match v with
    | none => Polynomial.X
    | some i => hasseDerivative (i : ℕ) (Polynomial.taylor a P)
  let shift : JetVariable r → DifferentialPolynomialOver F r := fun v =>
    match v with
    | none => MvPolynomial.X none + MvPolynomial.C a
    | some i => MvPolynomial.X (some i)
  let lhs : DifferentialPolynomialOver F r →+* Polynomial F :=
    (MvPolynomial.eval₂Hom Polynomial.C substTaylor).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C shift)
  let rhs : DifferentialPolynomialOver F r →+* Polynomial F :=
    (Polynomial.taylorAlgHom a).toRingHom.comp
      (MvPolynomial.eval₂Hom Polynomial.C subst)
  change lhs Q = rhs Q
  apply DFunLike.congr_fun
    (MvPolynomial.ringHom_ext (f := lhs) (g := rhs) ?_ ?_) Q
  · intro c
    simp [lhs, rhs, subst, substTaylor, shift]
  · intro v
    rcases v with (_ | i)
    · simp [lhs, rhs, subst, substTaylor, shift]
    · simp [lhs, rhs, subst, substTaylor, shift,
        hasseDerivative_taylor_comm]

/-- Translation of the independent variable commutes with partial
differentiation in every jet variable. -/
theorem pderiv_translateDifferential_some {r : ℕ}
    (a : F) (j : Fin (r + 1)) (Q : DifferentialPolynomialOver F r) :
    MvPolynomial.pderiv (some j) (translateDifferential a Q) =
      translateDifferential a (MvPolynomial.pderiv (some j) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [translateDifferential]
  | add p q hp hq =>
      rw [show translateDifferential a (p + q) =
        translateDifferential a p + translateDifferential a q by
          simp [translateDifferential]]
      rw [map_add, hp, hq]
      simp [translateDifferential]
  | mul_X p v hp =>
      rw [show translateDifferential a (p * MvPolynomial.X v) =
        translateDifferential a p * translateDifferential a (MvPolynomial.X v) by
          simp [translateDifferential]]
      rw [MvPolynomial.pderiv_mul, hp, MvPolynomial.pderiv_mul]
      rcases v with (_ | i)
      · simp [translateDifferential]
      · by_cases h : i = j
        · subst i
          simp [translateDifferential]
        · simp [translateDifferential, h]

end DifferentialJet

section GapCalculus

variable {R : Type*} [CommRing R]

/-- `GapAt s p` says that, between the constant coefficient and coefficient
`s`, the polynomial `p` has no terms. -/
def GapAt (s : ℕ) (p : Polynomial R) : Prop :=
  ∀ n, 0 < n → n < s → p.coeff n = 0

@[simp]
theorem gapAt_C (s : ℕ) (a : R) : GapAt s (Polynomial.C a) := by
  intro n hn _hns
  rw [Polynomial.coeff_C, if_neg hn.ne']

theorem GapAt.add {s : ℕ} {p q : Polynomial R}
    (hp : GapAt s p) (hq : GapAt s q) : GapAt s (p + q) := by
  intro n hn hns
  simp [Polynomial.coeff_add, hp n hn hns, hq n hn hns]

/-- Product rule for the first coefficient after a gap. -/
theorem coeff_mul_of_gap {s : ℕ} (hs : 0 < s) {p q : Polynomial R}
    (hp : GapAt s p) (hq : GapAt s q) :
    (p * q).coeff s = p.coeff 0 * q.coeff s + p.coeff s * q.coeff 0 := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Finset.add_sum_erase _ _ (by simp : 0 ∈ Finset.range (s + 1))]
  simp only [Nat.zero_add, Nat.sub_zero]
  congr 1
  rw [Finset.sum_eq_single s]
  · simp
  · intro i hi his
    have hi0 : 0 < i := by
      exact Nat.pos_of_ne_zero (Finset.mem_erase.mp hi).1
    have hi_range : i < s + 1 := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
    have his' : i < s := by omega
    simp [hp i hi0 his']
  · intro hsnot
    exact (hsnot (Finset.mem_erase.mpr ⟨hs.ne', by simp⟩)).elim

/-- Products preserve a coefficient gap. -/
theorem GapAt.mul {s : ℕ} {p q : Polynomial R}
    (hp : GapAt s p) (hq : GapAt s q) : GapAt s (p * q) := by
  intro n hn hns
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  by_cases hi : ij.1 = 0
  · rw [hi, zero_add] at hij
    rw [hi, hij, hq n hn hns, mul_zero]
  · have hi0 : 0 < ij.1 := Nat.pos_of_ne_zero hi
    by_cases hj : ij.2 = 0
    · rw [hj, add_zero] at hij
      rw [hj, hij, hp n hn hns, zero_mul]
    · have hj0 : 0 < ij.2 := Nat.pos_of_ne_zero hj
      have hi_lt : ij.1 < s := by omega
      simp [hp ij.1 hi0 hi_lt]

/-- Constant coefficient commutes with multivariate polynomial
specialization. -/
theorem coeff_zero_eval₂Hom {σ : Type*} (Q : MvPolynomial σ R)
    (g : σ → Polynomial R) :
    (MvPolynomial.eval₂Hom Polynomial.C g Q).coeff 0 =
      MvPolynomial.eval (fun v => (g v).coeff 0) Q := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  change Polynomial.evalRingHom 0
      (MvPolynomial.eval₂Hom Polynomial.C g Q) = _
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext a
    simp
  · funext v
    simp [Polynomial.coeff_zero_eq_eval_zero]
  · rfl

/-- Specializing a multivariate polynomial at arguments with a gap preserves
that gap. -/
theorem gapAt_eval₂Hom {σ : Type*} {s : ℕ} (Q : MvPolynomial σ R)
    (g : σ → Polynomial R) (hg : ∀ v, GapAt s (g v)) :
    GapAt s (MvPolynomial.eval₂Hom Polynomial.C g Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using gapAt_C s a
  | add p q hp hq =>
      simpa only [map_add] using hp.add hq
  | mul_X p v hp =>
      simpa only [map_mul, MvPolynomial.eval₂Hom_X'] using hp.mul (hg v)

/-- First-order coefficient formula for a multivariate specialization when
only one argument can vary at the first coefficient after a gap.  This is the
coefficient-level dual-number calculation used by regular Hensel lifting. -/
theorem coeff_eval₂Hom_of_single_gap {σ : Type*} [DecidableEq σ]
    {s : ℕ} (hs : 0 < s) (x : σ) (Q : MvPolynomial σ R)
    (g : σ → Polynomial R) (hg : ∀ v, GapAt s (g v))
    (hsingle : ∀ v, v ≠ x → (g v).coeff s = 0) :
    (MvPolynomial.eval₂Hom Polynomial.C g Q).coeff s =
      MvPolynomial.eval (fun v => (g v).coeff 0) (MvPolynomial.pderiv x Q) *
        (g x).coeff s := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [Polynomial.coeff_C, hs.ne']
  | add p q hp hq =>
      simp only [map_add, Polynomial.coeff_add, add_mul]
      rw [hp, hq]
  | mul_X p v hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X',
        coeff_mul_of_gap hs (gapAt_eval₂Hom p g hg) (hg v),
        MvPolynomial.pderiv_mul, MvPolynomial.eval_add,
        MvPolynomial.eval_mul, MvPolynomial.eval_X,
        coeff_zero_eval₂Hom]
      by_cases hvx : v = x
      · subst v
        simp only [MvPolynomial.pderiv_X_self, map_one, mul_one]
        rw [hp]
        ring
      · simp only [MvPolynomial.pderiv_X_of_ne hvx, map_zero, mul_zero,
          add_zero]
        rw [hp, hsingle v hvx]
        ring

/-- All coefficients strictly below `s` vanish.  This is the coefficient
form of divisibility by `X^s`. -/
def VanishBelow (s : ℕ) (p : Polynomial R) : Prop :=
  ∀ n, n < s → p.coeff n = 0

theorem vanishBelow_iff_X_pow_dvd {s : ℕ} {p : Polynomial R} :
    VanishBelow s p ↔ Polynomial.X ^ s ∣ p := by
  exact Polynomial.X_pow_dvd_iff.symm

theorem VanishBelow.add {s : ℕ} {p q : Polynomial R}
    (hp : VanishBelow s p) (hq : VanishBelow s q) :
    VanishBelow s (p + q) := by
  rw [vanishBelow_iff_X_pow_dvd] at hp hq ⊢
  exact dvd_add hp hq

theorem VanishBelow.mul_right {s : ℕ} {p : Polynomial R}
    (hp : VanishBelow s p) (q : Polynomial R) :
    VanishBelow s (p * q) := by
  rw [vanishBelow_iff_X_pow_dvd] at hp ⊢
  exact hp.mul_right q

theorem VanishBelow.mul_left {s : ℕ} {q : Polynomial R}
    (hq : VanishBelow s q) (p : Polynomial R) :
    VanishBelow s (p * q) := by
  rw [vanishBelow_iff_X_pow_dvd] at hq ⊢
  exact hq.mul_left p

/-- If the left factor first appears in degree `s`, only its degree-`s`
coefficient and the other factor's constant coefficient contribute in degree
`s`. -/
theorem coeff_mul_of_vanishBelow_left {s : ℕ} {p q : Polynomial R}
    (hp : VanishBelow s p) :
    (p * q).coeff s = p.coeff s * q.coeff 0 := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_eq_single s]
  · simp
  · intro i hi his
    have hi_range : i < s + 1 := Finset.mem_range.mp hi
    have his' : i < s := by omega
    simp [hp i his']
  · intro hsnot
    exact (hsnot (by simp)).elim

theorem coeff_mul_of_vanishBelow_right {s : ℕ} {p q : Polynomial R}
    (hq : VanishBelow s q) :
    (p * q).coeff s = p.coeff 0 * q.coeff s := by
  calc
    (p * q).coeff s = (q * p).coeff s := by rw [mul_comm]
    _ = q.coeff s * p.coeff 0 := coeff_mul_of_vanishBelow_left hq
    _ = p.coeff 0 * q.coeff s := mul_comm _ _

/-- Relative specialization preserves agreement below order `s`. -/
theorem vanishBelow_eval₂Hom_sub {σ : Type*} {s : ℕ}
    (Q : MvPolynomial σ R) (g h : σ → Polynomial R)
    (hgh : ∀ v, VanishBelow s (g v - h v)) :
    VanishBelow s
      (MvPolynomial.eval₂Hom Polynomial.C g Q -
        MvPolynomial.eval₂Hom Polynomial.C h Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
      simp [VanishBelow]
  | add p q hp hq =>
      rw [map_add, map_add]
      have heq :
          (MvPolynomial.eval₂Hom Polynomial.C g p +
              MvPolynomial.eval₂Hom Polynomial.C g q) -
            (MvPolynomial.eval₂Hom Polynomial.C h p +
              MvPolynomial.eval₂Hom Polynomial.C h q) =
          (MvPolynomial.eval₂Hom Polynomial.C g p -
              MvPolynomial.eval₂Hom Polynomial.C h p) +
            (MvPolynomial.eval₂Hom Polynomial.C g q -
              MvPolynomial.eval₂Hom Polynomial.C h q) := by ring
      rw [heq]
      exact hp.add hq
  | mul_X p v hp =>
      simp only [map_mul, MvPolynomial.eval₂Hom_X']
      rw [show
        MvPolynomial.eval₂Hom Polynomial.C g p * g v -
            MvPolynomial.eval₂Hom Polynomial.C h p * h v =
          (MvPolynomial.eval₂Hom Polynomial.C g p -
              MvPolynomial.eval₂Hom Polynomial.C h p) * g v +
            MvPolynomial.eval₂Hom Polynomial.C h p * (g v - h v) by ring]
      exact (hp.mul_right (g v)).add
        ((hgh v).mul_left (MvPolynomial.eval₂Hom Polynomial.C h p))

/-- Relative first-variation formula.  If two substitutions agree below
order `s`, and at order `s` can differ only in variable `x`, the coefficient
of their specialized difference is the evaluated partial derivative times
that one variable difference. -/
theorem coeff_eval₂Hom_sub_of_single_vanishBelow
    {σ : Type*} [DecidableEq σ] {s : ℕ} (hs : 0 < s) (x : σ)
    (Q : MvPolynomial σ R) (g h : σ → Polynomial R)
    (hgh : ∀ v, VanishBelow s (g v - h v))
    (hsingle : ∀ v, v ≠ x → (g v - h v).coeff s = 0) :
    (MvPolynomial.eval₂Hom Polynomial.C g Q -
        MvPolynomial.eval₂Hom Polynomial.C h Q).coeff s =
      MvPolynomial.eval (fun v => (h v).coeff 0)
          (MvPolynomial.pderiv x Q) *
        (g x - h x).coeff s := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [Polynomial.coeff_C, hs.ne']
  | add p q hp hq =>
      simp only [map_add, add_mul]
      rw [show
        (MvPolynomial.eval₂Hom Polynomial.C g p +
            MvPolynomial.eval₂Hom Polynomial.C g q) -
          (MvPolynomial.eval₂Hom Polynomial.C h p +
            MvPolynomial.eval₂Hom Polynomial.C h q) =
        (MvPolynomial.eval₂Hom Polynomial.C g p -
            MvPolynomial.eval₂Hom Polynomial.C h p) +
          (MvPolynomial.eval₂Hom Polynomial.C g q -
            MvPolynomial.eval₂Hom Polynomial.C h q) by ring,
        Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
      simp only [map_mul, MvPolynomial.eval₂Hom_X']
      rw [show
        MvPolynomial.eval₂Hom Polynomial.C g p * g v -
            MvPolynomial.eval₂Hom Polynomial.C h p * h v =
          (MvPolynomial.eval₂Hom Polynomial.C g p -
              MvPolynomial.eval₂Hom Polynomial.C h p) * g v +
            MvPolynomial.eval₂Hom Polynomial.C h p * (g v - h v) by ring,
        Polynomial.coeff_add,
        coeff_mul_of_vanishBelow_left
          (vanishBelow_eval₂Hom_sub p g h hgh),
        coeff_mul_of_vanishBelow_right (hgh v),
        MvPolynomial.pderiv_mul, map_add, map_mul,
        MvPolynomial.eval_X, coeff_zero_eval₂Hom]
      have hconst (w : σ) : (g w).coeff 0 = (h w).coeff 0 := by
        have hz := hgh w 0 hs
        simpa only [Polynomial.coeff_sub, sub_eq_zero] using hz
      rw [hconst v, hp]
      by_cases hvx : v = x
      · subst v
        simp only [MvPolynomial.pderiv_X_self, map_one, mul_one]
        ring
      · simp only [MvPolynomial.pderiv_X_of_ne hvx, map_zero, mul_zero,
          add_zero]
        rw [hsingle v hvx]
        ring

end GapCalculus

section RegularLift

variable {F : Type*} [Field F]

/-- Coefficient agreement strictly below an index. -/
def CoeffAgreeBelow (k : ℕ) (P P' : Polynomial F) : Prop :=
  ∀ n, n < k → P.coeff n = P'.coeff n

/-- The jet at the formal origin. -/
def jetAtZero {j : ℕ} (P : Polynomial F) : JetVariable j → F
  | none => 0
  | some i => P.coeff (i : ℕ)

/-- Evaluating a translated differential polynomial at the origin jet of a
translated candidate recovers evaluation at the original differential jet. -/
theorem eval_jetAtZero_translateDifferential {r : ℕ} (a : F)
    (Q : DifferentialPolynomialOver F r) (P : Polynomial F) :
    MvPolynomial.eval (jetAtZero (Polynomial.taylor a P))
        (translateDifferential a Q) =
      MvPolynomial.eval (differentialJet a P) Q := by
  let shift : JetVariable r → DifferentialPolynomialOver F r := fun v =>
    match v with
    | none => MvPolynomial.X none + MvPolynomial.C a
    | some i => MvPolynomial.X (some i)
  let lhs : DifferentialPolynomialOver F r →+* F :=
    (MvPolynomial.eval (jetAtZero (Polynomial.taylor a P))).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C shift)
  let rhs : DifferentialPolynomialOver F r →+* F :=
    MvPolynomial.eval (differentialJet a P)
  change lhs Q = rhs Q
  apply DFunLike.congr_fun
    (MvPolynomial.ringHom_ext (f := lhs) (g := rhs) ?_ ?_) Q
  · intro c
    simp [lhs, rhs, shift]
  · intro v
    rcases v with (_ | i)
    · simp [lhs, rhs, shift, jetAtZero, differentialJet]
    · simp [lhs, rhs, shift, jetAtZero, differentialJet,
        Polynomial.taylor_coeff]

/-- The highest jet variable in an order-`j` equation. -/
def lastJet (j : ℕ) : JetVariable j := some ⟨j, by omega⟩

/-- The jet variable of order `j`, viewed in an ambient equation of order
`r`.  Keeping the ambient type fixed is essential for iterating Hasse
strata while the highest variable still present decreases. -/
def jetAtOrder (r j : ℕ) (hjr : j ≤ r) : JetVariable r :=
  some ⟨j, Nat.lt_succ_of_le hjr⟩

/-- Every jet variable occurring in `Q` has index at most `j`.  The base
variable `X` (represented by `none`) is intentionally unrestricted. -/
def HasJetOrderAtMost {r : ℕ} (j : ℕ)
    (Q : DifferentialPolynomialOver F r) : Prop :=
  ∀ i : Fin (r + 1), some i ∈ Q.vars → (i : ℕ) ≤ j

/-- The ambient order is always a valid support bound. -/
theorem hasJetOrderAtMost_ambient {r : ℕ}
    (Q : DifferentialPolynomialOver F r) : HasJetOrderAtMost r Q := by
  intro i _hi
  exact Nat.le_of_lt_succ i.isLt

/-- Hasse partial differentiation preserves any active-order bound. -/
theorem HasJetOrderAtMost.partialHasse {r j : ℕ}
    {Q : DifferentialPolynomialOver F r} (h : HasJetOrderAtMost j Q)
    (x : JetVariable r) (m : ℕ) :
    HasJetOrderAtMost j (partialHasse x m Q) := by
  intro i hi
  exact h i (partialHasse_vars_subset x m Q hi)

/-- Extracting the top Hasse coefficient in the active variable lowers a
positive active-order bound by one. -/
theorem HasJetOrderAtMost.top_succ {r j : ℕ} (hjr : j + 1 ≤ r)
    {Q : DifferentialPolynomialOver F r}
    (h : HasJetOrderAtMost (j + 1) Q) :
    HasJetOrderAtMost j
      (RSListDecoding.partialHasse (jetAtOrder r (j + 1) hjr)
        (Q.degreeOf (jetAtOrder r (j + 1) hjr)) Q) := by
  intro i hi
  let x := jetAtOrder r (j + 1) hjr
  have hiQ : some i ∈ Q.vars := partialHasse_vars_subset x (Q.degreeOf x) Q hi
  have hi_le : (i : ℕ) ≤ j + 1 := h i hiQ
  have hi_ne : (i : ℕ) ≠ j + 1 := by
    intro hieq
    have heq : (some i : JetVariable r) = x := by
      simp [x, jetAtOrder, Fin.ext_iff, hieq]
    apply partialHasse_top_notMem_vars x Q
    simpa only [heq] using hi
  omega

/-- After extracting the top coefficient in order zero, no jet variable
remains; the result is a polynomial in the independent variable alone. -/
theorem HasJetOrderAtMost.top_zero_noJet {r : ℕ}
    {Q : DifferentialPolynomialOver F r} (h : HasJetOrderAtMost 0 Q) :
    ∀ i : Fin (r + 1), some i ∉
      (RSListDecoding.partialHasse (jetAtOrder r 0 (Nat.zero_le r))
        (Q.degreeOf (jetAtOrder r 0 (Nat.zero_le r))) Q).vars := by
  intro i hi
  let x := jetAtOrder r 0 (Nat.zero_le r)
  have hiQ : some i ∈ Q.vars := partialHasse_vars_subset x (Q.degreeOf x) Q hi
  have hi_zero : (i : ℕ) = 0 := Nat.eq_zero_of_le_zero (h i hiQ)
  have heq : (some i : JetVariable r) = x := by
    simp [x, jetAtOrder, Fin.ext_iff, hi_zero]
  apply partialHasse_top_notMem_vars x Q
  simpa only [heq] using hi

/-- Translating the independent variable introduces no new jet variables. -/
theorem HasJetOrderAtMost.translate {r j : ℕ} {a : F}
    {Q : DifferentialPolynomialOver F r} (h : HasJetOrderAtMost j Q) :
    HasJetOrderAtMost j (translateDifferential a Q) := by
  classical
  intro i hi
  let shift : JetVariable r → DifferentialPolynomialOver F r := fun v =>
    match v with
    | none => MvPolynomial.X none + MvPolynomial.C a
    | some k => MvPolynomial.X (some k)
  have htranslate : translateDifferential a Q = MvPolynomial.bind₁ shift Q := by
    change MvPolynomial.eval₂Hom MvPolynomial.C shift Q = _
    exact DFunLike.congr_fun (MvPolynomial.eval₂Hom_C_eq_bind₁ shift) Q
  have hi' : some i ∈ (MvPolynomial.bind₁ shift Q).vars := by
    rwa [htranslate] at hi
  obtain ⟨v, hvQ, hiv⟩ := MvPolynomial.mem_vars_bind₁ shift Q hi'
  rcases v with (_ | k)
  · have hmem := MvPolynomial.vars_add_subset
        (MvPolynomial.X none : DifferentialPolynomialOver F r)
        (MvPolynomial.C a) hiv
    simp [shift] at hmem
  · have hik : i = k := by simpa [shift] using hiv
    subst k
    exact h i hvQ

/-- Agreement of polynomial coefficients below `k` gives the shifted
agreement needed for the `i`-th Hasse derivatives. -/
theorem vanishBelow_hasseDerivative_sub {P P' : Polynomial F} {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) (hagree : CoeffAgreeBelow k P P') :
    VanishBelow (k - j)
      (hasseDerivative i P - hasseDerivative i P') := by
  intro n hn
  simp only [Polynomial.coeff_sub, coeff_hasseDerivative]
  have hindex : n + i < k := by omega
  rw [hagree (n + i) hindex]
  ring

/-- At the first coefficient not known to agree, lower Hasse derivatives do
not contribute to the highest-jet variation. -/
theorem coeff_hasseDerivative_sub_eq_zero_of_lt
    {P P' : Polynomial F} {i j k : ℕ}
    (hij : i < j) (hjk : j < k) (hagree : CoeffAgreeBelow k P P') :
    (hasseDerivative i P - hasseDerivative i P').coeff (k - j) = 0 := by
  simp only [Polynomial.coeff_sub, coeff_hasseDerivative]
  have hindex : k - j + i < k := by omega
  rw [hagree (k - j + i) hindex]
  ring

/-- The highest Hasse derivative exposes the next unknown coefficient with
the expected binomial scalar. -/
theorem coeff_hasseDerivative_sub_at_frontier
    {P P' : Polynomial F} {j k : ℕ} (hjk : j ≤ k) :
    (hasseDerivative j P - hasseDerivative j P').coeff (k - j) =
      (k.choose j : F) * (P.coeff k - P'.coeff k) := by
  simp only [Polynomial.coeff_sub, coeff_hasseDerivative]
  rw [Nat.sub_add_cancel hjk]
  ring

/-- The constant coefficients of the differential substitution are exactly
the formal-origin jet. -/
theorem coeff_zero_differentialSubstitution {j : ℕ} (P : Polynomial F) :
    (fun v : JetVariable j =>
      (match v with
        | none => Polynomial.X
        | some i => hasseDerivative (i : ℕ) P).coeff 0) = jetAtZero P := by
  funext v
  rcases v with (_ | i)
  · simp [jetAtZero]
  · simp [jetAtZero, coeff_hasseDerivative]

/-- One regular lifting step: once coefficients below `k` agree, the
coefficient at `k` is forced. -/
theorem regular_lift_coefficient_eq
    {q D j k : ℕ} [CharP F q]
    (hq : q.Prime) (hjk : j < k) (hkD : k ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F j) (P P' : Polynomial F)
    (hP : differentialSpecializationOver Q P = 0)
    (hP' : differentialSpecializationOver Q P' = 0)
    (hsep : MvPolynomial.eval (jetAtZero P')
      (MvPolynomial.pderiv (lastJet j) Q) ≠ 0)
    (hagree : CoeffAgreeBelow k P P') :
    P.coeff k = P'.coeff k := by
  let g : JetVariable j → Polynomial F := fun v => match v with
    | none => Polynomial.X
    | some i => hasseDerivative (i : ℕ) P
  let h : JetVariable j → Polynomial F := fun v => match v with
    | none => Polynomial.X
    | some i => hasseDerivative (i : ℕ) P'
  have hs : 0 < k - j := Nat.sub_pos_of_lt hjk
  have hgh : ∀ v, VanishBelow (k - j) (g v - h v) := by
    intro v
    rcases v with (_ | i)
    · simp [g, h, VanishBelow]
    · exact vanishBelow_hasseDerivative_sub i.is_le hjk.le hagree
  have hsingle : ∀ v, v ≠ lastJet j → (g v - h v).coeff (k - j) = 0 := by
    intro v hv
    rcases v with (_ | i)
    · simp [g, h]
    · have hi : (i : ℕ) < j := by
        have hle : (i : ℕ) ≤ j := by omega
        have hne : (i : ℕ) ≠ j := by
          intro heq
          apply hv
          simp [lastJet, Fin.ext_iff, heq]
        omega
      exact coeff_hasseDerivative_sub_eq_zero_of_lt hi hjk hagree
  have hvariation := coeff_eval₂Hom_sub_of_single_vanishBelow
    hs (lastJet j) Q g h hgh hsingle
  have hg_spec : MvPolynomial.eval₂Hom Polynomial.C g Q = 0 := by
    change differentialSpecializationOver Q P = 0
    exact hP
  have hh_spec : MvPolynomial.eval₂Hom Polynomial.C h Q = 0 := by
    change differentialSpecializationOver Q P' = 0
    exact hP'
  rw [hg_spec, hh_spec, sub_zero, Polynomial.coeff_zero] at hvariation
  rw [coeff_zero_differentialSubstitution P'] at hvariation
  have hfrontier :
      (g (lastJet j) - h (lastJet j)).coeff (k - j) =
        (k.choose j : F) * (P.coeff k - P'.coeff k) := by
    simpa [g, h, lastJet] using
      (coeff_hasseDerivative_sub_at_frontier (F := F) hjk.le)
  rw [hfrontier] at hvariation
  have hchoose : (k.choose j : F) ≠ 0 :=
    natCast_choose_ne_zero_of_lt_char hq hjk.le hkD hDq
  have hproduct :
      MvPolynomial.eval (jetAtZero P')
          (MvPolynomial.pderiv (lastJet j) Q) *
        ((k.choose j : F) * (P.coeff k - P'.coeff k)) = 0 :=
    hvariation.symm
  rcases mul_eq_zero.mp hproduct with hsep0 | htail
  · exact (hsep hsep0).elim
  · rcases mul_eq_zero.mp htail with hchoose0 | hcoeff
    · exact (hchoose hchoose0).elim
    · exact sub_eq_zero.mp hcoeff

/-- A regular initial jet has at most one degree-`D` lift when `D` is below
the characteristic.  This is the Hensel uniqueness statement used by the
refinement, proved coefficient by coefficient. -/
theorem regular_lift_unique
    {q D j : ℕ} [CharP F q]
    (hq : q.Prime) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F j) (P P' : Polynomial F)
    (hdegP : P.degree ≤ D) (hdegP' : P'.degree ≤ D)
    (hP : differentialSpecializationOver Q P = 0)
    (hP' : differentialSpecializationOver Q P' = 0)
    (hsep : MvPolynomial.eval (jetAtZero P')
      (MvPolynomial.pderiv (lastJet j) Q) ≠ 0)
    (hinit : ∀ n, n ≤ j → P.coeff n = P'.coeff n) :
    P = P' := by
  apply Polynomial.ext
  intro k
  by_cases hkD : k ≤ D
  · induction k using Nat.strong_induction_on with
    | h k ih =>
        by_cases hkj : k ≤ j
        · exact hinit k hkj
        · apply regular_lift_coefficient_eq hq (lt_of_not_ge hkj) hkD hDq
            Q P P' hP hP' hsep
          intro n hnk
          exact ih n hnk (hnk.le.trans hkD)
  · have hDk : D < k := lt_of_not_ge hkD
    have hPk : P.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        (hdegP.trans_lt (WithBot.coe_lt_coe.mpr hDk))
    have hP'k : P'.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        (hdegP'.trans_lt (WithBot.coe_lt_coe.mpr hDk))
    rw [hPk, hP'k]

/-- One regular lifting step inside a fixed ambient jet-variable type.  Only
variables that actually occur in `Q` matter, so an equation whose active
order has fallen to `j` forces the next coefficient exactly as an order-`j`
equation does. -/
theorem regular_lift_coefficient_eq_of_orderAtMost
    {q D r j k : ℕ} [CharP F q]
    (hq : q.Prime) (hjr : j ≤ r) (hjk : j < k) (hkD : k ≤ D)
    (hDq : D < q) (Q : DifferentialPolynomialOver F r)
    (horder : HasJetOrderAtMost j Q) (P P' : Polynomial F)
    (hP : differentialSpecializationOver Q P = 0)
    (hP' : differentialSpecializationOver Q P' = 0)
    (hsep : MvPolynomial.eval (jetAtZero P')
      (MvPolynomial.pderiv (jetAtOrder r j hjr) Q) ≠ 0)
    (hagree : CoeffAgreeBelow k P P') :
    P.coeff k = P'.coeff k := by
  classical
  let x : JetVariable r := jetAtOrder r j hjr
  let g : JetVariable r → Polynomial F := fun v => match v with
    | none => Polynomial.X
    | some i => hasseDerivative (i : ℕ) P
  let h : JetVariable r → Polynomial F := fun v => match v with
    | none => Polynomial.X
    | some i => hasseDerivative (i : ℕ) P'
  let g' : JetVariable r → Polynomial F := fun v =>
    if v ∈ Q.vars then g v else h v
  have hxvars : x ∈ Q.vars := by
    by_contra hx
    have hzero := MvPolynomial.pderiv_eq_zero_of_notMem_vars hx
    rw [hzero] at hsep
    simp at hsep
  have hg'eq : MvPolynomial.eval₂Hom Polynomial.C g' Q =
      MvPolynomial.eval₂Hom Polynomial.C g Q := by
    apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
    intro v hv _
    simp [g', hv]
  have hs : 0 < k - j := Nat.sub_pos_of_lt hjk
  have hgh : ∀ v, VanishBelow (k - j) (g' v - h v) := by
    intro v
    by_cases hv : v ∈ Q.vars
    · rcases v with (_ | i)
      · simp [g', g, h, hv, VanishBelow]
      · simp only [g', hv, if_pos, g, h]
        exact vanishBelow_hasseDerivative_sub (horder i hv) hjk.le hagree
    · simp [g', hv, VanishBelow]
  have hsingle : ∀ v, v ≠ x → (g' v - h v).coeff (k - j) = 0 := by
    intro v hvx
    by_cases hv : v ∈ Q.vars
    · rcases v with (_ | i)
      · simp [g', g, h, hv]
      · have hi_le : (i : ℕ) ≤ j := horder i hv
        have hi_ne : (i : ℕ) ≠ j := by
          intro hij
          apply hvx
          simp [x, jetAtOrder, Fin.ext_iff, hij]
        have hi_lt : (i : ℕ) < j := lt_of_le_of_ne hi_le hi_ne
        simp only [g', hv, if_pos, g, h]
        exact coeff_hasseDerivative_sub_eq_zero_of_lt hi_lt hjk hagree
    · simp [g', hv]
  have hvariation := coeff_eval₂Hom_sub_of_single_vanishBelow
    hs x Q g' h hgh hsingle
  have hg_spec : MvPolynomial.eval₂Hom Polynomial.C g Q = 0 := by
    change differentialSpecializationOver Q P = 0
    exact hP
  have hg'_spec : MvPolynomial.eval₂Hom Polynomial.C g' Q = 0 := by
    rw [hg'eq, hg_spec]
  have hh_spec : MvPolynomial.eval₂Hom Polynomial.C h Q = 0 := by
    change differentialSpecializationOver Q P' = 0
    exact hP'
  rw [hg'_spec, hh_spec, sub_zero, Polynomial.coeff_zero] at hvariation
  rw [coeff_zero_differentialSubstitution P'] at hvariation
  have hfrontier :
      (g' x - h x).coeff (k - j) =
        (k.choose j : F) * (P.coeff k - P'.coeff k) := by
    rw [show g' x = g x by simp [g', hxvars]]
    simpa [g, h, x, jetAtOrder] using
      (coeff_hasseDerivative_sub_at_frontier (F := F) hjk.le)
  rw [hfrontier] at hvariation
  have hchoose : (k.choose j : F) ≠ 0 :=
    natCast_choose_ne_zero_of_lt_char hq hjk.le hkD hDq
  have hproduct :
      MvPolynomial.eval (jetAtZero P')
          (MvPolynomial.pderiv x Q) *
        ((k.choose j : F) * (P.coeff k - P'.coeff k)) = 0 :=
    hvariation.symm
  rcases mul_eq_zero.mp hproduct with hsep0 | htail
  · exact (hsep hsep0).elim
  · rcases mul_eq_zero.mp htail with hchoose0 | hcoeff
    · exact (hchoose hchoose0).elim
    · exact sub_eq_zero.mp hcoeff

/-- A regular initial jet of active order `j` has at most one bounded-degree
lift, even when the equation is kept in a larger ambient jet-variable type. -/
theorem regular_lift_unique_of_orderAtMost
    {q D r j : ℕ} [CharP F q]
    (hq : q.Prime) (hjr : j ≤ r) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F r) (horder : HasJetOrderAtMost j Q)
    (P P' : Polynomial F) (hdegP : P.degree ≤ D)
    (hdegP' : P'.degree ≤ D)
    (hP : differentialSpecializationOver Q P = 0)
    (hP' : differentialSpecializationOver Q P' = 0)
    (hsep : MvPolynomial.eval (jetAtZero P')
      (MvPolynomial.pderiv (jetAtOrder r j hjr) Q) ≠ 0)
    (hinit : ∀ n, n ≤ j → P.coeff n = P'.coeff n) :
    P = P' := by
  apply Polynomial.ext
  intro k
  by_cases hkD : k ≤ D
  · induction k using Nat.strong_induction_on with
    | h k ih =>
        by_cases hkj : k ≤ j
        · exact hinit k hkj
        · apply regular_lift_coefficient_eq_of_orderAtMost hq hjr
            (lt_of_not_ge hkj) hkD hDq Q horder P P' hP hP' hsep
          intro n hnk
          exact ih n hnk (hnk.le.trans hkD)
  · have hDk : D < k := lt_of_not_ge hkD
    have hPk : P.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        (hdegP.trans_lt (WithBot.coe_lt_coe.mpr hDk))
    have hP'k : P'.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt
        (hdegP'.trans_lt (WithBot.coe_lt_coe.mpr hDk))
    rw [hPk, hP'k]

/-- Arbitrary-point form of regular uniqueness in a fixed ambient
jet-variable type. -/
theorem regular_lift_unique_at_of_orderAtMost
    {q D r j : ℕ} [CharP F q]
    (hq : q.Prime) (hjr : j ≤ r) (hjD : j ≤ D) (hDq : D < q)
    (a : F) (Q : DifferentialPolynomialOver F r)
    (horder : HasJetOrderAtMost j Q) (P P' : Polynomial F)
    (hdegP : P.degree ≤ D) (hdegP' : P'.degree ≤ D)
    (hP : differentialSpecializationOver Q P = 0)
    (hP' : differentialSpecializationOver Q P' = 0)
    (hsep : MvPolynomial.eval (differentialJet a P')
      (MvPolynomial.pderiv (jetAtOrder r j hjr) Q) ≠ 0)
    (hinit : ∀ n, n ≤ j →
      (hasseDerivative n P).eval a = (hasseDerivative n P').eval a) :
    P = P' := by
  apply Polynomial.taylor_injective a
  apply regular_lift_unique_of_orderAtMost hq hjr hjD hDq
      (translateDifferential a Q) horder.translate
      (Polynomial.taylor a P) (Polynomial.taylor a P')
  · simpa only [Polynomial.degree_taylor] using hdegP
  · simpa only [Polynomial.degree_taylor] using hdegP'
  · rw [differentialSpecializationOver_translate, hP]
    simp
  · rw [differentialSpecializationOver_translate, hP']
    simp
  · change MvPolynomial.eval (jetAtZero (Polynomial.taylor a P'))
      (MvPolynomial.pderiv (some ⟨j, Nat.lt_succ_of_le hjr⟩)
        (translateDifferential a Q)) ≠ 0
    rw [pderiv_translateDifferential_some,
      eval_jetAtZero_translateDifferential]
    exact hsep
  · intro n hn
    simpa only [Polynomial.taylor_coeff] using hinit n hn

/-- Arbitrary-point form of regular Hensel uniqueness.  Translation reduces
it to `regular_lift_unique`; the initial data are the Hasse coefficients at
the chosen expansion point. -/
theorem regular_lift_unique_at
    {q D j : ℕ} [CharP F q]
    (hq : q.Prime) (hjD : j ≤ D) (hDq : D < q)
    (a : F) (Q : DifferentialPolynomialOver F j) (P P' : Polynomial F)
    (hdegP : P.degree ≤ D) (hdegP' : P'.degree ≤ D)
    (hP : differentialSpecializationOver Q P = 0)
    (hP' : differentialSpecializationOver Q P' = 0)
    (hsep : MvPolynomial.eval (differentialJet a P')
      (MvPolynomial.pderiv (lastJet j) Q) ≠ 0)
    (hinit : ∀ n, n ≤ j →
      (hasseDerivative n P).eval a = (hasseDerivative n P').eval a) :
    P = P' := by
  apply Polynomial.taylor_injective a
  apply regular_lift_unique hq hjD hDq (translateDifferential a Q)
      (Polynomial.taylor a P) (Polynomial.taylor a P')
  · simpa only [Polynomial.degree_taylor] using hdegP
  · simpa only [Polynomial.degree_taylor] using hdegP'
  · rw [differentialSpecializationOver_translate, hP]
    simp
  · rw [differentialSpecializationOver_translate, hP']
    simp
  · change MvPolynomial.eval (jetAtZero (Polynomial.taylor a P'))
      (MvPolynomial.pderiv (some ⟨j, by omega⟩)
        (translateDifferential a Q)) ≠ 0
    rw [pderiv_translateDifferential_some,
      eval_jetAtZero_translateDifferential]
    exact hsep
  · intro n hn
    simpa only [Polynomial.taylor_coeff] using hinit n hn

end RegularLift

section FibrePolynomial

variable {F : Type*} [Field F] {σ : Type*} [DecidableEq σ]

/-- Evaluating a multivariate polynomial at polynomial arguments has degree
bounded by the corresponding weighted total degree. -/
theorem natDegree_eval₂Hom_le_weightedTotalDegree
    (Q : MvPolynomial σ F) (g : σ → Polynomial F) (w : σ → ℕ)
    (hg : ∀ v, (g v).natDegree ≤ w v) :
    (MvPolynomial.eval₂Hom Polynomial.C g Q).natDegree ≤
      Q.weightedTotalDegree w := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum Q]
  simp only [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro u hu
  rw [MvPolynomial.eval₂Hom_monomial]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le u.support
    (fun v => (g v) ^ u v)).trans ?_
  calc
    ∑ v ∈ u.support, ((g v) ^ u v).natDegree ≤
        ∑ v ∈ u.support, u v * w v := by
      apply Finset.sum_le_sum
      intro v _hv
      exact Polynomial.natDegree_pow_le.trans
        (Nat.mul_le_mul_left (u v) (hg v))
    _ = Finsupp.weight w u := by
      rw [Finsupp.weight_apply]
      simp only [Finsupp.sum, nsmul_eq_mul, Nat.cast_id]
    _ ≤ Q.weightedTotalDegree w :=
      MvPolynomial.le_weightedTotalDegree _ hu

/-- Every polynomial substituted for a jet variable has degree at most its
Kopparty weight.  This is the coefficient-ring-generic version used after
passing to a Galois field. -/
theorem natDegree_specializationVariableOver_le
    {r D : ℕ} (P : Polynomial F) (hP : P.natDegree ≤ D)
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

/-- Differential specialization over an arbitrary field does not exceed the
weighted-degree budget. -/
theorem natDegree_differentialSpecializationOver_le_weightedTotalDegree
    {r D : ℕ} (Q : DifferentialPolynomialOver F r)
    (P : Polynomial F) (hP : P.natDegree ≤ D) :
    (differentialSpecializationOver Q P).natDegree ≤
      Q.weightedTotalDegree (jetWeight (r := r) D) := by
  exact natDegree_eval₂Hom_le_weightedTotalDegree Q
    (fun v : JetVariable r => match v with
      | none => Polynomial.X
      | some j => hasseDerivative (j : ℕ) P)
    (jetWeight D) (natDegree_specializationVariableOver_le P hP)

/-- A nonzero specialization whose weighted-degree budget is smaller than
the finite field has a nonvanishing evaluation point.  This is the exact
coverage lemma for selecting an expansion point in the root refinement. -/
theorem exists_nonvanishing_specialization_point
    [Fintype F] {r D : ℕ} (Q : DifferentialPolynomialOver F r)
    (P : Polynomial F) (hP : P.natDegree ≤ D)
    (hne : differentialSpecializationOver Q P ≠ 0)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) <
      Fintype.card F) :
    ∃ a : F, (differentialSpecializationOver Q P).eval a ≠ 0 := by
  apply Polynomial.exists_eval_ne_zero_of_natDegree_lt_card _ hne
  simpa only [Cardinal.mk_fintype, Nat.cast_lt] using
    (natDegree_differentialSpecializationOver_le_weightedTotalDegree
      Q P hP).trans_lt hweight

/-- If the top Hasse stratum in one coordinate has nonzero specialization,
then a solution belongs to a regular lower stratum at some field point.  The
stratum and point are obtained constructively from the finite derivative
chain and the weighted-degree bound. -/
theorem exists_regular_partialHasse_point
    [Fintype F] {r D q : ℕ} [CharP F q]
    (x : JetVariable r) (Q : DifferentialPolynomialOver F r)
    (P : Polynomial F) (hP : P.natDegree ≤ D)
    (hsolution : differentialSpecializationOver Q P = 0)
    (htop : differentialSpecializationOver
      (partialHasse x (Q.degreeOf x) Q) P ≠ 0)
    (hcoord : Q.degreeOf x < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) <
      Fintype.card F) :
    ∃ m < Q.degreeOf x,
      differentialSpecializationOver (partialHasse x m Q) P = 0 ∧
      ∃ a : F, MvPolynomial.eval (differentialJet a P)
        (MvPolynomial.pderiv x (partialHasse x m Q)) ≠ 0 := by
  obtain ⟨m, hm, hmzero, hmnext⟩ := exists_zero_succ_ne_zero
    (fun n => differentialSpecializationOver (partialHasse x n Q) P)
    (by simpa using hsolution) htop
  refine ⟨m, hm, hmzero, ?_⟩
  have hmchar : m + 1 < q := (Nat.succ_le_of_lt hm).trans_lt hcoord
  obtain ⟨a, ha⟩ := exists_nonvanishing_specialization_point
    (partialHasse x (m + 1) Q) P hP hmnext
    ((weightedTotalDegree_partialHasse_le
      (jetWeight (r := r) D) x (m + 1) Q).trans_lt hweight)
  refine ⟨a, ?_⟩
  rw [← eval_differentialSpecializationOver]
  have hsep : differentialSpecializationOver
      (MvPolynomial.pderiv x (partialHasse x m Q)) P =
      (m + 1) • differentialSpecializationOver
        (partialHasse x (m + 1) Q) P := by
    rw [pderiv_partialHasse]
    change MvPolynomial.eval₂Hom Polynomial.C _ ((m + 1) •
      partialHasse x (m + 1) Q) = _
    rw [map_nsmul]
    rfl
  rw [hsep]
  change Polynomial.evalRingHom a ((m + 1) •
    differentialSpecializationOver (partialHasse x (m + 1) Q) P) ≠ 0
  rw [map_nsmul, nsmul_eq_mul]
  apply mul_ne_zero
  · exact (CharP.cast_eq_zero_iff F q (m + 1)).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) hmchar)
  · exact ha

/-- The least Hasse stratum whose differential specialization is nonzero.
It is defined as zero when every stratum specializes to zero; all uses of
the value below carry an existence hypothesis. -/
noncomputable def firstNonzeroPartialHasseIndex {r : ℕ}
    (x : JetVariable r) (Q : DifferentialPolynomialOver F r)
    (P : Polynomial F) : ℕ := by
  classical
  exact if h : ∃ n, differentialSpecializationOver
      (partialHasse x n Q) P ≠ 0 then Nat.find h else 0

theorem firstNonzeroPartialHasseIndex_spec {r : ℕ}
    (x : JetVariable r) (Q : DifferentialPolynomialOver F r)
    (P : Polynomial F)
    (h : ∃ n, differentialSpecializationOver
      (partialHasse x n Q) P ≠ 0) :
    differentialSpecializationOver
      (partialHasse x (firstNonzeroPartialHasseIndex x Q P) Q) P ≠ 0 := by
  classical
  simp only [firstNonzeroPartialHasseIndex, dif_pos h]
  exact Nat.find_spec h

theorem firstNonzeroPartialHasseIndex_min {r : ℕ}
    (x : JetVariable r) (Q : DifferentialPolynomialOver F r)
    (P : Polynomial F)
    (h : ∃ n, differentialSpecializationOver
      (partialHasse x n Q) P ≠ 0)
    {m : ℕ} (hm : m < firstNonzeroPartialHasseIndex x Q P) :
    differentialSpecializationOver (partialHasse x m Q) P = 0 := by
  classical
  by_contra hmne
  have hle := Nat.find_min' h hmne
  have hle' : firstNonzeroPartialHasseIndex x Q P ≤ m := by
    simpa only [firstNonzeroPartialHasseIndex, dif_pos h] using hle
  exact (not_le_of_gt hm) hle'

theorem firstNonzeroPartialHasseIndex_le {r : ℕ}
    (x : JetVariable r) (Q : DifferentialPolynomialOver F r)
    (P : Polynomial F)
    (h : ∃ n, differentialSpecializationOver
      (partialHasse x n Q) P ≠ 0)
    {m : ℕ}
    (hm : differentialSpecializationOver (partialHasse x m Q) P ≠ 0) :
    firstNonzeroPartialHasseIndex x Q P ≤ m := by
  classical
  simpa only [firstNonzeroPartialHasseIndex, dif_pos h] using Nat.find_min' h hm

/-- A deterministic nonvanishing evaluation point for a univariate
polynomial, with zero as the unused fallback. -/
noncomputable def firstNonvanishingPoint [Fintype F]
    (S : Polynomial F) : F := by
  classical
  exact if h : ∃ a, S.eval a ≠ 0 then Classical.choose h else 0

theorem firstNonvanishingPoint_spec [Fintype F] (S : Polynomial F)
    (h : ∃ a, S.eval a ≠ 0) : S.eval (firstNonvanishingPoint S) ≠ 0 := by
  classical
  simp only [firstNonvanishingPoint, dif_pos h]
  exact Classical.choose_spec h

/-- View a multivariate polynomial as a univariate polynomial in `x`, after
fixing every other variable. -/
def fibrePolynomial (x : σ) (a : σ → F) (Q : MvPolynomial σ F) :
    Polynomial F :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun v => if v = x then Polynomial.X else Polynomial.C (a v)) Q

/-- The fibre construction is scalar evaluation of the coefficient
polynomials after isolating the active variable. -/
theorem fibrePolynomial_eq_map_isolate (x : σ) (a : σ → F)
    (Q : MvPolynomial σ F) :
    fibrePolynomial x a Q =
      (isolateVariableEquiv x Q).map
        (MvPolynomial.eval fun y : {z : σ // z ≠ x} => a y.1) := by
  let lhs : MvPolynomial σ F →+* Polynomial F :=
    MvPolynomial.eval₂Hom Polynomial.C
      (fun v => if v = x then Polynomial.X else Polynomial.C (a v))
  let rhs : MvPolynomial σ F →+* Polynomial F :=
    (Polynomial.mapRingHom
      (MvPolynomial.eval fun y : {z : σ // z ≠ x} => a y.1)).comp
        (isolateVariableEquiv x).toAlgHom.toRingHom
  change lhs Q = rhs Q
  apply DFunLike.congr_fun
    (MvPolynomial.ringHom_ext (f := lhs) (g := rhs) ?_ ?_) Q
  · intro c
    simp [lhs, rhs, isolateVariableEquiv]
  · intro y
    by_cases hy : y = x
    · subst y
      simp [lhs, rhs]
    · simp [lhs, rhs, hy, isolateVariableEquiv_X_ne]

/-- Fibre formation commutes with Hasse differentiation in the active
coordinate. -/
theorem fibrePolynomial_partialHasse (x : σ) (a : σ → F)
    (m : ℕ) (Q : MvPolynomial σ F) :
    fibrePolynomial x a (partialHasse x m Q) =
      hasseDerivative m (fibrePolynomial x a Q) := by
  rw [fibrePolynomial_eq_map_isolate, fibrePolynomial_eq_map_isolate,
    isolateVariableEquiv_partialHasse]
  exact (hasseDerivative_map
    (MvPolynomial.eval fun y : {z : σ // z ≠ x} => a y.1)
    (isolateVariableEquiv x Q) m).symm

/-- Evaluation of the fibre polynomial restores ordinary multivariate
evaluation. -/
theorem fibrePolynomial_eval (x : σ) (a : σ → F)
    (Q : MvPolynomial σ F) (z : F) :
    (fibrePolynomial x a Q).eval z =
      MvPolynomial.eval (Function.update a x z) Q := by
  rw [fibrePolynomial]
  change Polynomial.evalRingHom z
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun v => if v = x then Polynomial.X else Polynomial.C (a v)) Q) = _
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext c
    simp
  · funext v
    by_cases hv : v = x
    · subst v
      simp
    · simp [hv]
  · rfl

/-- The fibre degree is at most the coordinate degree. -/
theorem fibrePolynomial_natDegree_le_degreeOf (x : σ) (a : σ → F)
    (Q : MvPolynomial σ F) :
    (fibrePolynomial x a Q).natDegree ≤ Q.degreeOf x := by
  rw [← MvPolynomial.weightedTotalDegree_piSingle x Q]
  apply natDegree_eval₂Hom_le_weightedTotalDegree
  intro v
  by_cases hv : v = x
  · subst v
    simp [fibrePolynomial]
  · simp [fibrePolynomial, hv]

set_option maxHeartbeats 600000 in
/-- Differentiating a fibre polynomial is the same as taking the partial
derivative before forming the fibre. -/
theorem derivative_fibrePolynomial (x : σ) (a : σ → F)
    (Q : MvPolynomial σ F) :
    (fibrePolynomial x a Q).derivative =
      fibrePolynomial x a (MvPolynomial.pderiv x Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [fibrePolynomial]
  | add p q hp hq =>
      rw [show fibrePolynomial x a (p + q) =
        fibrePolynomial x a p + fibrePolynomial x a q by
          simp [fibrePolynomial], Polynomial.derivative_add, hp, hq]
      simp [fibrePolynomial]
  | mul_X p v hp =>
      rw [show fibrePolynomial x a (p * MvPolynomial.X v) =
        fibrePolynomial x a p *
          (if v = x then Polynomial.X else Polynomial.C (a v)) by
            simp [fibrePolynomial], Polynomial.derivative_mul, hp,
        MvPolynomial.pderiv_mul]
      by_cases hv : v = x
      · subst v
        simp [fibrePolynomial, MvPolynomial.pderiv_X_self]
      · simp [fibrePolynomial, hv, MvPolynomial.pderiv_X_of_ne hv]

/-- A regular root witnesses that its fibre polynomial is nonzero. -/
theorem fibrePolynomial_ne_zero_of_pderiv_eval_ne_zero
    (x : σ) (a : σ → F) (Q : MvPolynomial σ F) (z : F)
    (h : MvPolynomial.eval (Function.update a x z)
      (MvPolynomial.pderiv x Q) ≠ 0) :
    fibrePolynomial x a Q ≠ 0 := by
  intro hzero
  have hderiv : (fibrePolynomial x a Q).derivative = 0 := by rw [hzero]; simp
  rw [derivative_fibrePolynomial] at hderiv
  have heval := congrArg (fun p : Polynomial F => p.eval z) hderiv
  rw [fibrePolynomial_eval] at heval
  exact h (by simpa using heval)

end FibrePolynomial

section RegularFibres

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Taylor coefficients strictly below the active jet order. -/
def lowerJet {j : ℕ} (P : Polynomial F) : Fin j → F :=
  fun i => P.coeff (i : ℕ)

/-- Turn the fixed lower-jet data into a full assignment.  The value at the
last jet is a dummy; `fibrePolynomial_eval` overwrites it. -/
def lowerJetAssignment {j : ℕ} (b : Fin j → F) : JetVariable j → F
  | none => 0
  | some i => if hi : (i : ℕ) < j then b ⟨i, hi⟩ else 0

/-- Updating the dummy last coordinate recovers the complete origin jet. -/
theorem update_lowerJetAssignment_lastJet {j : ℕ} (P : Polynomial F)
    (b : Fin j → F) (hb : lowerJet P = b) :
    Function.update (lowerJetAssignment b) (lastJet j) (P.coeff j) =
      jetAtZero P := by
  funext v
  rcases v with (_ | i)
  · simp [lowerJetAssignment, lastJet, jetAtZero]
  · by_cases hi : (i : ℕ) < j
    · have hne : (some i : JetVariable j) ≠ lastJet j := by
        intro heq
        simp [lastJet, Fin.ext_iff] at heq
        omega
      simp only [Function.update, hne, ↓reduceIte, lowerJetAssignment,
        hi, dite_true, jetAtZero]
      have hb_i := congrFun hb ⟨i, hi⟩
      exact hb_i.symm
    · have hieq : (i : ℕ) = j := by omega
      have heq : (some i : JetVariable j) = lastJet j := by
        simp [lastJet, Fin.ext_iff, hieq]
      rw [heq]
      simp [Function.update, jetAtZero, lastJet]

/-- Regular solutions at the formal origin for an order-`j` equation. -/
def regularSolutionsAtZero {j : ℕ} (D : ℕ)
    (Q : DifferentialPolynomialOver F j) :
    Finset (Polynomial.degreeLT F (D + 1)) := by
  classical
  exact (differentialSolutionsOver D Q).filter fun P =>
    MvPolynomial.eval (jetAtZero P)
      (MvPolynomial.pderiv (lastJet j) Q) ≠ 0

@[simp]
theorem mem_regularSolutionsAtZero {j D : ℕ}
    (Q : DifferentialPolynomialOver F j)
    (P : Polynomial.degreeLT F (D + 1)) :
    P ∈ regularSolutionsAtZero D Q ↔
      differentialSpecializationOver Q P = 0 ∧
      MvPolynomial.eval (jetAtZero P)
        (MvPolynomial.pderiv (lastJet j) Q) ≠ 0 := by
  classical
  simp [regularSolutionsAtZero, mem_differentialSolutionsOver]

/-- The degree-bounded subtype really consists of polynomials of degree at
most `D`. -/
theorem degree_le_of_mem_degreeLT_succ {D : ℕ}
    (P : Polynomial.degreeLT F (D + 1)) : P.1.degree ≤ D := by
  rw [← Polynomial.mem_degreeLE,
    ← Polynomial.degreeLT_succ_eq_degreeLE]
  exact P.2

end RegularFibres

section RootFibres

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A nonzero univariate polynomial has at most its degree many roots in a
finite field.  Stating this for a filtered `univ` makes it directly usable by
the finite evaluator in the root recursion. -/
theorem card_filter_eval_eq_zero_le_natDegree (p : Polynomial F) (hp : p ≠ 0) :
    (Finset.univ.filter fun x : F ↦ p.eval x = 0).card ≤ p.natDegree := by
  classical
  calc
    (Finset.univ.filter fun x : F ↦ p.eval x = 0).card ≤ p.roots.toFinset.card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).2 hx.2)
    _ ≤ p.roots.card := Multiset.toFinset_card_le p.roots
    _ ≤ p.natDegree := Polynomial.card_roots' p

/-- The same estimate with an externally supplied degree cap. -/
theorem card_filter_eval_eq_zero_le (p : Polynomial F) (hp : p ≠ 0)
    {t : ℕ} (hdegree : p.natDegree ≤ t) :
    (Finset.univ.filter fun x : F ↦ p.eval x = 0).card ≤ t := by
  classical
  exact (card_filter_eval_eq_zero_le_natDegree p hp).trans hdegree

/-- Field points at which a polynomial does not vanish. -/
def nonvanishingPoints (p : Polynomial F) : Finset F :=
  Finset.univ.filter fun a => p.eval a ≠ 0

/-- A degree-`Delta` nonzero polynomial is nonzero at at least
`|F|-Delta` points. -/
theorem card_sub_degree_le_nonvanishingPoints
    (p : Polynomial F) (hp : p ≠ 0) {Delta : ℕ}
    (hdegree : p.natDegree ≤ Delta) :
    Fintype.card F - Delta ≤ (nonvanishingPoints p).card := by
  classical
  let zeros := Finset.univ.filter fun a : F => p.eval a = 0
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ) (fun a : F => p.eval a = 0)
  have hzeros : zeros.card ≤ Delta :=
    (card_filter_eval_eq_zero_le_natDegree p hp).trans hdegree
  have hcard : zeros.card + (nonvanishingPoints p).card = Fintype.card F := by
    simpa [zeros, nonvanishingPoints] using hpartition
  omega

end RootFibres

section RegularFibreCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The constant coefficient of a solved differential equation vanishes at
the solution's origin jet. -/
theorem eval_jetAtZero_eq_zero_of_solution {j : ℕ}
    (Q : DifferentialPolynomialOver F j) (P : Polynomial F)
    (hP : differentialSpecializationOver Q P = 0) :
    MvPolynomial.eval (jetAtZero P) Q = 0 := by
  rw [← coeff_zero_differentialSubstitution P,
    ← coeff_zero_eval₂Hom]
  change (differentialSpecializationOver Q P).coeff 0 = 0
  rw [hP]
  exact Polynomial.coeff_zero 0

/-- A solution in a fixed lower-jet fibre supplies a root of the associated
univariate fibre polynomial. -/
theorem fibrePolynomial_eval_active_eq_zero_of_solution
    {j : ℕ} (Q : DifferentialPolynomialOver F j) (P : Polynomial F)
    (b : Fin j → F) (hb : lowerJet P = b)
    (hP : differentialSpecializationOver Q P = 0) :
    (fibrePolynomial (lastJet j) (lowerJetAssignment b) Q).eval
      (P.coeff j) = 0 := by
  rw [fibrePolynomial_eval,
    update_lowerJetAssignment_lastJet P b hb]
  exact eval_jetAtZero_eq_zero_of_solution Q P hP

/-- Regularity makes the associated univariate fibre polynomial nonzero. -/
theorem fibrePolynomial_ne_zero_of_regular_solution
    {j : ℕ} (Q : DifferentialPolynomialOver F j) (P : Polynomial F)
    (b : Fin j → F) (hb : lowerJet P = b)
    (hsep : MvPolynomial.eval (jetAtZero P)
      (MvPolynomial.pderiv (lastJet j) Q) ≠ 0) :
    fibrePolynomial (lastJet j) (lowerJetAssignment b) Q ≠ 0 := by
  apply fibrePolynomial_ne_zero_of_pderiv_eval_ne_zero
    (lastJet j) (lowerJetAssignment b) Q (P.coeff j)
  rw [update_lowerJetAssignment_lastJet P b hb]
  exact hsep

/-- On a fixed lower-jet fibre, the active coefficient is injective among
regular solutions. -/
theorem activeCoeff_injOn_regularSolutionsAtZero_fibre
    {q D j : ℕ} [CharP F q]
    (hq : q.Prime) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F j) (b : Fin j → F) :
    Set.InjOn (fun P : Polynomial.degreeLT F (D + 1) => P.1.coeff j)
      (↑((regularSolutionsAtZero D Q).filter
        (fun P : Polynomial.degreeLT F (D + 1) => lowerJet P.1 = b)) : Set _) := by
  intro P hP P' hP' hcoeff
  have hP_parts := Finset.mem_filter.mp hP
  have hP'_parts := Finset.mem_filter.mp hP'
  have hP_reg := (mem_regularSolutionsAtZero Q P).mp hP_parts.1
  have hP'_reg := (mem_regularSolutionsAtZero Q P').mp hP'_parts.1
  apply Subtype.ext
  apply regular_lift_unique hq hjD hDq Q P P'
      (degree_le_of_mem_degreeLT_succ P)
      (degree_le_of_mem_degreeLT_succ P')
      hP_reg.1 hP'_reg.1 hP'_reg.2
  intro n hnj
  by_cases hn : n < j
  · let i : Fin j := ⟨n, hn⟩
    calc
      P.1.coeff n = lowerJet P i := rfl
      _ = b i := congrFun hP_parts.2 i
      _ = lowerJet P' i := (congrFun hP'_parts.2 i).symm
      _ = P'.1.coeff n := rfl
  · have hnj_eq : n = j := by omega
    simpa [hnj_eq] using hcoeff

/-- For fixed lower Taylor coefficients, regular solutions inject into the
roots of a single univariate fibre polynomial. -/
theorem card_regularSolutionsAtZero_fibre_le_degreeOf
    {q D j : ℕ} [CharP F q]
    (hq : q.Prime) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F j) (b : Fin j → F) :
    ((regularSolutionsAtZero D Q).filter
      (fun P : Polynomial.degreeLT F (D + 1) => lowerJet P.1 = b)).card ≤
      Q.degreeOf (lastJet j) := by
  classical
  let s := (regularSolutionsAtZero D Q).filter
    (fun P : Polynomial.degreeLT F (D + 1) => lowerJet P.1 = b)
  let p := fibrePolynomial (lastJet j) (lowerJetAssignment b) Q
  by_cases hs : s.Nonempty
  · obtain ⟨P₀, hP₀⟩ := hs
    have hP₀_parts := Finset.mem_filter.mp hP₀
    have hP₀_reg := (mem_regularSolutionsAtZero Q P₀).mp hP₀_parts.1
    have hp_ne : p ≠ 0 :=
      fibrePolynomial_ne_zero_of_regular_solution Q P₀ b
        hP₀_parts.2 hP₀_reg.2
    let roots : Finset F := Finset.univ.filter fun z => p.eval z = 0
    have hmap : Set.MapsTo (fun P : Polynomial.degreeLT F (D + 1) =>
        P.1.coeff j) (↑s : Set _) (↑roots : Set F) := by
      intro P hP
      have hP_parts := Finset.mem_filter.mp hP
      have hP_reg := (mem_regularSolutionsAtZero Q P).mp hP_parts.1
      change P.1.coeff j ∈ roots
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,
        fibrePolynomial_eval_active_eq_zero_of_solution
          Q P b hP_parts.2 hP_reg.1⟩
    have hinj : Set.InjOn (fun P : Polynomial.degreeLT F (D + 1) =>
        P.1.coeff j) (↑s : Set _) :=
      activeCoeff_injOn_regularSolutionsAtZero_fibre hq hjD hDq Q b
    calc
      ((regularSolutionsAtZero D Q).filter
          (fun P : Polynomial.degreeLT F (D + 1) => lowerJet P.1 = b)).card =
          s.card := rfl
      _ ≤ roots.card := Finset.card_le_card_of_injOn _ hmap hinj
      _ ≤ p.natDegree := card_filter_eval_eq_zero_le_natDegree p hp_ne
      _ ≤ Q.degreeOf (lastJet j) :=
        fibrePolynomial_natDegree_le_degreeOf
          (lastJet j) (lowerJetAssignment b) Q
  · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [s] at hsempty
    rw [hsempty]
    exact Nat.zero_le _

/-- Coordinate degree cap version of the regular fibre estimate. -/
theorem card_regularSolutionsAtZero_fibre_le
    {q D j t : ℕ} [CharP F q]
    (hq : q.Prime) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F j)
    (hdegree : Q.degreeOf (lastJet j) ≤ t) (b : Fin j → F) :
    ((regularSolutionsAtZero D Q).filter
      (fun P : Polynomial.degreeLT F (D + 1) => lowerJet P.1 = b)).card ≤ t :=
  (card_regularSolutionsAtZero_fibre_le_degreeOf hq hjD hDq Q b).trans hdegree

end RegularFibreCount

section ActiveOrderCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Taylor data strictly below the active order at an arbitrary point. -/
def lowerJetAt {j : ℕ} (a : F) (P : Polynomial F) : Fin j → F :=
  fun i => (hasseDerivative (i : ℕ) P).eval a

/-- Assignment determined by an expansion point and the Taylor data below
the active order.  Inactive higher jets receive a dummy zero. -/
def lowerJetAssignmentAt {r j : ℕ} (hjr : j ≤ r)
    (a : F) (b : Fin j → F) : JetVariable r → F
  | none => a
  | some i => if hi : (i : ℕ) < j then b ⟨i, hi⟩ else 0

/-- Filling the active coordinate restores the differential jet on every
variable at or below the active order. -/
theorem update_lowerJetAssignmentAt_jetAtOrder {r j : ℕ} (hjr : j ≤ r)
    (a : F) (P : Polynomial F) (v : JetVariable r)
    (hv : match v with | none => True | some i => (i : ℕ) ≤ j) :
    Function.update (lowerJetAssignmentAt hjr a (lowerJetAt a P))
        (jetAtOrder r j hjr) ((hasseDerivative j P).eval a) v =
      differentialJet a P v := by
  rcases v with (_ | i)
  · simp [lowerJetAssignmentAt, jetAtOrder, differentialJet]
  · by_cases hi : (i : ℕ) < j
    · have hne : (some i : JetVariable r) ≠ jetAtOrder r j hjr := by
        intro heq
        simp [jetAtOrder, Fin.ext_iff] at heq
        omega
      simp [Function.update, hne, lowerJetAssignmentAt, lowerJetAt,
        differentialJet, hi]
    · have hieq : (i : ℕ) = j := by omega
      have heq : (some i : JetVariable r) = jetAtOrder r j hjr := by
        simp [jetAtOrder, Fin.ext_iff, hieq]
      rw [heq]
      simp [Function.update, differentialJet, jetAtOrder]

/-- Solutions for which the top Hasse coefficient in the current active
variable has nonzero specialization.  These are exactly the solutions
handled at this order; the complementary branch descends one order. -/
def activeOrderSolutions {r : ℕ} (D : ℕ) (x : JetVariable r)
    (Q : DifferentialPolynomialOver F r) :
    Finset (Polynomial.degreeLT F (D + 1)) :=
  (differentialSolutionsOver D Q).filter fun P =>
    differentialSpecializationOver
      (partialHasse x (Q.degreeOf x) Q) P ≠ 0

@[simp]
theorem mem_activeOrderSolutions {r D : ℕ} (x : JetVariable r)
    (Q : DifferentialPolynomialOver F r)
    (P : Polynomial.degreeLT F (D + 1)) :
    P ∈ activeOrderSolutions D x Q ↔
      differentialSpecializationOver Q P = 0 ∧
      differentialSpecializationOver
        (partialHasse x (Q.degreeOf x) Q) P ≠ 0 := by
  classical
  simp [activeOrderSolutions, mem_differentialSolutionsOver]

/-- The deterministic expansion point attached to an active-order
solution. -/
noncomputable def activeExpansionPoint {r : ℕ} (x : JetVariable r)
    (Q : DifferentialPolynomialOver F r) (P : Polynomial F) : F :=
  firstNonvanishingPoint
    (differentialSpecializationOver
      (partialHasse x (firstNonzeroPartialHasseIndex x Q P) Q) P)

/-- Counting key at active order `j`: the expansion point followed by the
Taylor data below order `j`. -/
noncomputable def activeOrderKey {r j D : ℕ} (hjr : j ≤ r)
    (Q : DifferentialPolynomialOver F r)
    (P : Polynomial.degreeLT F (D + 1)) : F × (Fin j → F) :=
  let a := activeExpansionPoint (jetAtOrder r j hjr) Q P
  (a, lowerJetAt a P)

/-- The active Taylor coefficient attached to a solution. -/
noncomputable def activeOrderValue {r j D : ℕ} (hjr : j ≤ r)
    (Q : DifferentialPolynomialOver F r)
    (P : Polynomial.degreeLT F (D + 1)) : F :=
  let a := activeExpansionPoint (jetAtOrder r j hjr) Q P
  (hasseDerivative j P.1).eval a

/-- Facts supplied by the canonical least nonzero Hasse stratum and its
canonical nonvanishing point. -/
theorem activeOrderChoice_spec {q r D j : ℕ} [CharP F q]
    (hjr : j ≤ r) (Q : DifferentialPolynomialOver F r)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < Fintype.card F)
    (P : Polynomial.degreeLT F (D + 1))
    (hP : P ∈ activeOrderSolutions D (jetAtOrder r j hjr) Q) :
    let x := jetAtOrder r j hjr
    let n := firstNonzeroPartialHasseIndex x Q P
    let a := activeExpansionPoint x Q P
    0 < n ∧ n ≤ Q.degreeOf x ∧
      differentialSpecializationOver (partialHasse x (n - 1) Q) P = 0 ∧
      (differentialSpecializationOver (partialHasse x n Q) P).eval a ≠ 0 := by
  classical
  let x := jetAtOrder r j hjr
  have hparts := (mem_activeOrderSolutions x Q P).mp hP
  let d := Q.degreeOf x
  have hexists : ∃ n, differentialSpecializationOver
      (partialHasse x n Q) P ≠ 0 := ⟨d, hparts.2⟩
  let n := firstNonzeroPartialHasseIndex x Q P
  have hnne : differentialSpecializationOver (partialHasse x n Q) P ≠ 0 :=
    firstNonzeroPartialHasseIndex_spec x Q P hexists
  have hnle : n ≤ d := firstNonzeroPartialHasseIndex_le x Q P hexists hparts.2
  have hnpos : 0 < n := by
    by_contra hn
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    apply hnne
    simpa [hnzero] using hparts.1
  have hmzero : differentialSpecializationOver
      (partialHasse x (n - 1) Q) P = 0 :=
    firstNonzeroPartialHasseIndex_min x Q P hexists (by omega)
  have hnatdeg : P.1.natDegree ≤ D := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact degree_le_of_mem_degreeLT_succ P
  have hexistsPoint : ∃ a : F,
      (differentialSpecializationOver (partialHasse x n Q) P).eval a ≠ 0 :=
    exists_nonvanishing_specialization_point (partialHasse x n Q) P hnatdeg hnne
      ((weightedTotalDegree_partialHasse_le
        (jetWeight (r := r) D) x n Q).trans_lt hweight)
  refine ⟨hnpos, hnle, hmzero, ?_⟩
  exact firstNonvanishingPoint_spec _ hexistsPoint

/-- An active solution together with any expansion point at which its least
nonzero Hasse stratum remains nonzero. -/
abbrev ActivePointPair {r : ℕ} (D : ℕ) (x : JetVariable r)
    (Q : DifferentialPolynomialOver F r) :=
  Σ P : ↥(activeOrderSolutions D x Q),
    ↥(nonvanishingPoints
      (differentialSpecializationOver
        (partialHasse x
          (firstNonzeroPartialHasseIndex x Q P.1) Q) P.1))

/-- The key of an arbitrary nonvanishing expansion-point pair. -/
def activePointKey {r j D : ℕ} (hjr : j ≤ r)
    (Q : DifferentialPolynomialOver F r)
    (z : ActivePointPair D (jetAtOrder r j hjr) Q) :
    F × (Fin j → F) :=
  (z.2.1, lowerJetAt z.2.1 z.1.1)

/-- The active Taylor coefficient of an expansion-point pair. -/
def activePointValue {r j D : ℕ} (hjr : j ≤ r)
    (Q : DifferentialPolynomialOver F r)
    (z : ActivePointPair D (jetAtOrder r j hjr) Q) : F :=
  (hasseDerivative j z.1.1.1).eval z.2.1

/-- Every active solution supplies at least `|F|-Delta` admissible expansion
points when all relevant specializations have degree at most `Delta`. -/
theorem activeOrder_card_mul_card_sub_le_activePointPair
    {r D j Delta : ℕ} (hjr : j ≤ r)
    (Q : DifferentialPolynomialOver F r)
    (hDelta : Q.weightedTotalDegree (jetWeight (r := r) D) ≤ Delta) :
    (activeOrderSolutions D (jetAtOrder r j hjr) Q).card *
        (Fintype.card F - Delta) ≤
      Fintype.card (ActivePointPair D (jetAtOrder r j hjr) Q) := by
  classical
  let x := jetAtOrder r j hjr
  let active := activeOrderSolutions D x Q
  rw [Fintype.card_sigma]
  calc
    active.card * (Fintype.card F - Delta) =
        ∑ _P : ↥active, (Fintype.card F - Delta) := by
      simp [active]
    _ ≤ ∑ P : ↥active,
        Fintype.card ↥(nonvanishingPoints
          (differentialSpecializationOver
            (partialHasse x
              (firstNonzeroPartialHasseIndex x Q P.1) Q) P.1)) := by
      apply Finset.sum_le_sum
      intro P _hP
      rw [Fintype.card_coe]
      have hactive := (mem_activeOrderSolutions x Q P.1).mp P.2
      have hexists : ∃ n, differentialSpecializationOver
          (partialHasse x n Q) P.1 ≠ 0 :=
        ⟨Q.degreeOf x, hactive.2⟩
      have hne := firstNonzeroPartialHasseIndex_spec x Q P.1 hexists
      apply card_sub_degree_le_nonvanishingPoints _ hne
      exact (natDegree_differentialSpecializationOver_le_weightedTotalDegree
          (partialHasse x
            (firstNonzeroPartialHasseIndex x Q P.1) Q) P.1
          (by
            rw [Polynomial.natDegree_le_iff_degree_le]
            exact degree_le_of_mem_degreeLT_succ P.1)).trans
        ((weightedTotalDegree_partialHasse_le
          (jetWeight (r := r) D) x
          (firstNonzeroPartialHasseIndex x Q P.1) Q).trans hDelta)

/-- The arbitrary point in an `ActivePointPair` satisfies the same regular
stratum facts as the former canonical point. -/
theorem activePointPair_spec {q r D j : ℕ} [CharP F q]
    (hjr : j ≤ r) (Q : DifferentialPolynomialOver F r)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < Fintype.card F)
    (z : ActivePointPair D (jetAtOrder r j hjr) Q) :
    let x := jetAtOrder r j hjr
    let n := firstNonzeroPartialHasseIndex x Q z.1.1
    let a := z.2.1
    0 < n ∧ n ≤ Q.degreeOf x ∧
      differentialSpecializationOver (partialHasse x (n - 1) Q) z.1.1 = 0 ∧
      (differentialSpecializationOver (partialHasse x n Q) z.1.1).eval a ≠ 0 := by
  classical
  let x := jetAtOrder r j hjr
  let n := firstNonzeroPartialHasseIndex x Q z.1.1
  have hbase := activeOrderChoice_spec hjr Q hweight z.1.1 z.1.2
  dsimp only [x, n] at hbase
  refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, ?_⟩
  exact (Finset.mem_filter.mp z.2.2).2

end ActiveOrderCount

section CountingShell

variable {F A : Type*} [Fintype F]

/-- The certificate attached to a solution by the refined recursion: a
highest active jet order `j`, followed by the base point and `j` lower Taylor
coefficients. -/
abbrev RootRefinementKey (F : Type*) (r : ℕ) :=
  Σ j : Fin (r + 1), Fin ((j : ℕ) + 1) → F

/-- The dependent key space has the geometric-sum cardinality appearing in
the refined theorem. -/
theorem card_rootRefinementKey {q e r : ℕ}
    (hcard : Fintype.card F = q ^ e) :
    Fintype.card (RootRefinementKey F r) =
      rootCountGeometricFactor q e r := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin, hcard]
  rw [Fin.sum_univ_eq_sum_range (fun j => (q ^ e) ^ (j + 1)) (r + 1)]
  simp only [rootCountGeometricFactor, pow_mul]

/-- Finite fiber counting, in the exact orientation needed by the root
recursion.  Notice that the per-fiber bound is `t`, not `t + 1`. -/
theorem card_le_mul_card_of_fibers [Fintype A] [DecidableEq A]
    {B : Type*} [Fintype B] [DecidableEq B]
    (s : Finset A) (key : A → B) (t : ℕ)
    (hfiber : ∀ b : B, (s.filter fun a => key a = b).card ≤ t) :
    s.card ≤ t * Fintype.card B := by
  rw [Finset.card_eq_sum_card_fiberwise
    (t := Finset.univ) (f := key) (fun _ _ => Finset.mem_univ _)]
  calc
    (∑ b ∈ Finset.univ, (s.filter fun a => key a = b).card) ≤
        ∑ _b : B, t := by
      apply Finset.sum_le_sum
      intro b _hb
      exact hfiber b
    _ = Fintype.card B * t := by simp
    _ = t * Fintype.card B := Nat.mul_comm _ _

/-- Counting by refinement keys gives precisely the geometric factor. -/
theorem card_le_rootCountGeometricFactor [Fintype A] [DecidableEq A]
    [DecidableEq F] {q e r t : ℕ}
    (hcard : Fintype.card F = q ^ e)
    (s : Finset A) (key : A → RootRefinementKey F r)
    (hfiber : ∀ b, (s.filter fun a => key a = b).card ≤ t) :
    s.card ≤ t * rootCountGeometricFactor q e r := by
  rw [← card_rootRefinementKey hcard]
  exact card_le_mul_card_of_fibers s key t hfiber

end CountingShell

section ActiveOrderFibreCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Equal Taylor data through the active order give equal evaluations of
every Hasse stratum of an equation supported through that order. -/
theorem eval_partialHasse_eq_of_initialJet {r j : ℕ}
    (a : F) (Q : DifferentialPolynomialOver F r)
    (horder : HasJetOrderAtMost j Q) (x : JetVariable r) (m : ℕ)
    (P P' : Polynomial F)
    (hinit : ∀ n, n ≤ j →
      (hasseDerivative n P).eval a = (hasseDerivative n P').eval a) :
    MvPolynomial.eval (differentialJet a P) (partialHasse x m Q) =
      MvPolynomial.eval (differentialJet a P') (partialHasse x m Q) := by
  change MvPolynomial.eval₂Hom (RingHom.id F) (differentialJet a P)
      (partialHasse x m Q) =
    MvPolynomial.eval₂Hom (RingHom.id F) (differentialJet a P')
      (partialHasse x m Q)
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro v hv _
  rcases v with (_ | i)
  · simp [differentialJet]
  · simp only [differentialJet]
    exact hinit i (horder i (partialHasse_vars_subset x m Q hv))

set_option maxHeartbeats 800000 in
/-- For two arbitrary nonvanishing expansion-point pairs with the same key
and active value, the least nonzero Hasse strata coincide. -/
theorem firstNonzeroIndex_eq_of_activePoint_key_value
    {q r D j : ℕ} [CharP F q]
    (hjr : j ≤ r) (Q : DifferentialPolynomialOver F r)
    (horder : HasJetOrderAtMost j Q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < Fintype.card F)
    (z z' : ActivePointPair D (jetAtOrder r j hjr) Q)
    (hkey : activePointKey hjr Q z = activePointKey hjr Q z')
    (hvalue : activePointValue hjr Q z = activePointValue hjr Q z') :
    firstNonzeroPartialHasseIndex (jetAtOrder r j hjr) Q z.1.1 =
      firstNonzeroPartialHasseIndex (jetAtOrder r j hjr) Q z'.1.1 := by
  classical
  let x := jetAtOrder r j hjr
  let n := firstNonzeroPartialHasseIndex x Q z.1.1
  let n' := firstNonzeroPartialHasseIndex x Q z'.1.1
  let a := z.2.1
  have hkey_fst := congrArg Prod.fst hkey
  have ha : z'.2.1 = a := by
    change z.2.1 = z'.2.1 at hkey_fst
    exact hkey_fst.symm
  have hkey_snd := congrArg Prod.snd hkey
  have hlower : lowerJetAt (j := j) a z.1.1 =
      lowerJetAt (j := j) a z'.1.1 := by
    change lowerJetAt (j := j) z.2.1 z.1.1 =
      lowerJetAt (j := j) z'.2.1 z'.1.1 at hkey_snd
    rw [ha] at hkey_snd
    exact hkey_snd
  have hinit : ∀ k, k ≤ j →
      (hasseDerivative k z.1.1.1).eval a =
        (hasseDerivative k z'.1.1.1).eval a := by
    intro k hkj
    by_cases hk : k < j
    · exact congrFun hlower ⟨k, hk⟩
    · have hkeq : k = j := by omega
      subst k
      change (hasseDerivative j z.1.1.1).eval z.2.1 =
        (hasseDerivative j z'.1.1.1).eval z'.2.1 at hvalue
      rw [ha] at hvalue
      exact hvalue
  have hspec := activePointPair_spec hjr Q hweight z
  have hspec' := activePointPair_spec hjr Q hweight z'
  dsimp only [x, n, a] at hspec
  dsimp only [x, n'] at hspec'
  rw [ha] at hspec'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hz := firstNonzeroPartialHasseIndex_min x Q z'.1.1
        ⟨Q.degreeOf x, (mem_activeOrderSolutions x Q z'.1.1).mp z'.1.2 |>.2⟩ hlt
    have heval := congrArg (fun S : Polynomial F => S.eval a) hz
    rw [eval_differentialSpecializationOver] at heval
    simp only [Polynomial.eval_zero] at heval
    have heq := eval_partialHasse_eq_of_initialJet a Q horder x n
      z.1.1.1 z'.1.1.1 hinit
    exact hspec.2.2.2 (by
      rw [eval_differentialSpecializationOver]
      simpa [n] using heq.trans heval)
  · have hz := firstNonzeroPartialHasseIndex_min x Q z.1.1
        ⟨Q.degreeOf x, (mem_activeOrderSolutions x Q z.1.1).mp z.1.2 |>.2⟩ hgt
    have heval := congrArg (fun S : Polynomial F => S.eval a) hz
    rw [eval_differentialSpecializationOver] at heval
    simp only [Polynomial.eval_zero] at heval
    have heq := eval_partialHasse_eq_of_initialJet a Q horder x n'
      z.1.1.1 z'.1.1.1 hinit
    exact hspec'.2.2.2 (by
      rw [eval_differentialSpecializationOver]
      simpa [n'] using heq.symm.trans heval)

set_option maxHeartbeats 2000000 in
/-- Within a fixed arbitrary expansion-point/lower-jet key, the active
Taylor value is injective on solution-point pairs. -/
theorem activePointValue_injOn
    {q r D j t : ℕ} [CharP F q]
    (hq : q.Prime) (hjr : j ≤ r) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F r) (horder : HasJetOrderAtMost j Q)
    (hdegree : Q.degreeOf (jetAtOrder r j hjr) ≤ t) (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < Fintype.card F)
    (b : F × (Fin j → F)) :
    Set.InjOn (activePointValue hjr Q)
      {z : ActivePointPair D (jetAtOrder r j hjr) Q |
        activePointKey hjr Q z = b} := by
  classical
  intro z hz z' hz' hvalue
  have hkey : activePointKey hjr Q z = activePointKey hjr Q z' :=
    hz.trans hz'.symm
  have hn_eq := firstNonzeroIndex_eq_of_activePoint_key_value
    hjr Q horder hweight z z' hkey hvalue
  let x := jetAtOrder r j hjr
  let n := firstNonzeroPartialHasseIndex x Q z.1.1
  let a := z.2.1
  have hkey_fst := congrArg Prod.fst hkey
  have ha : z'.2.1 = a := by
    change z.2.1 = z'.2.1 at hkey_fst
    exact hkey_fst.symm
  have hkey_snd := congrArg Prod.snd hkey
  have hlower : lowerJetAt (j := j) a z.1.1 =
      lowerJetAt (j := j) a z'.1.1 := by
    change lowerJetAt (j := j) z.2.1 z.1.1 =
      lowerJetAt (j := j) z'.2.1 z'.1.1 at hkey_snd
    rw [ha] at hkey_snd
    exact hkey_snd
  have hinit : ∀ k, k ≤ j →
      (hasseDerivative k z.1.1.1).eval a =
        (hasseDerivative k z'.1.1.1).eval a := by
    intro k hkj
    by_cases hk : k < j
    · exact congrFun hlower ⟨k, hk⟩
    · have hkeq : k = j := by omega
      subst k
      change (hasseDerivative j z.1.1.1).eval z.2.1 =
        (hasseDerivative j z'.1.1.1).eval z'.2.1 at hvalue
      rw [ha] at hvalue
      exact hvalue
  have hspec := activePointPair_spec hjr Q hweight z
  have hspec' := activePointPair_spec hjr Q hweight z'
  dsimp only [x, n, a] at hspec
  dsimp only [x] at hspec'
  have hprev' : differentialSpecializationOver
      (partialHasse x (n - 1) Q) z'.1.1 = 0 := by
    have hprev := hspec'.2.2.1
    rw [← hn_eq] at hprev
    exact hprev
  have hnonzero' :
      (differentialSpecializationOver (partialHasse x n Q) z'.1.1).eval a ≠ 0 := by
    let n' := firstNonzeroPartialHasseIndex x Q z'.1.1
    let a' : F := z'.2.1
    have hnonzero :
        (differentialSpecializationOver
          (partialHasse x n' Q) z'.1.1).eval a' ≠ 0 := by
      exact (Finset.mem_filter.mp z'.2.2).2
    have hnn' : n = n' := hn_eq
    have haa' : a' = a := ha
    simpa only [hnn', haa'] using hnonzero
  have hpoly : z.1.1.1 = z'.1.1.1 := by
    apply regular_lift_unique_at_of_orderAtMost hq hjr hjD hDq a
      (partialHasse x (n - 1) Q) (horder.partialHasse x (n - 1))
      z.1.1.1 z'.1.1.1
    · exact degree_le_of_mem_degreeLT_succ z.1.1
    · exact degree_le_of_mem_degreeLT_succ z'.1.1
    · exact hspec.2.2.1
    · exact hprev'
    · have hnq : n < q := hspec.2.1.trans_lt (hdegree.trans_lt htq)
      have hnpos : 0 < n := by simpa [n] using hspec.1
      rw [pderiv_partialHasse]
      have hnstep : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
      rw [hnstep, map_nsmul, nsmul_eq_mul]
      apply mul_ne_zero
      · exact (CharP.cast_eq_zero_iff F q n).not.mpr
          (Nat.not_dvd_of_pos_of_lt hnpos hnq)
      · rw [← eval_differentialSpecializationOver]
        exact hnonzero'
    · exact hinit
  have hfirst : z.1 = z'.1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hpoly
  have hdegreeLT : z.1.1 = z'.1.1 := congrArg Subtype.val hfirst
  apply Sigma.ext hfirst
  apply (Subtype.heq_iff_coe_eq (fun u => by
    rw [hdegreeLT])).2
  exact ha.symm

/-- On a fixed active-order key, equality of the active Taylor coefficient
forces equality of the canonical Hasse stratum. -/
theorem firstNonzeroIndex_eq_of_key_value
    {q r D j : ℕ} [CharP F q]
    (hjr : j ≤ r) (Q : DifferentialPolynomialOver F r)
    (horder : HasJetOrderAtMost j Q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < Fintype.card F)
    (P P' : Polynomial.degreeLT F (D + 1))
    (hP : P ∈ activeOrderSolutions D (jetAtOrder r j hjr) Q)
    (hP' : P' ∈ activeOrderSolutions D (jetAtOrder r j hjr) Q)
    (hkey : activeOrderKey hjr Q P = activeOrderKey hjr Q P')
    (hvalue : activeOrderValue hjr Q P = activeOrderValue hjr Q P') :
    firstNonzeroPartialHasseIndex (jetAtOrder r j hjr) Q P =
      firstNonzeroPartialHasseIndex (jetAtOrder r j hjr) Q P' := by
  classical
  let x := jetAtOrder r j hjr
  let n := firstNonzeroPartialHasseIndex x Q P
  let n' := firstNonzeroPartialHasseIndex x Q P'
  let a := activeExpansionPoint x Q P
  have hkey_fst := congrArg Prod.fst hkey
  have ha : activeExpansionPoint x Q P' = a := by
    simpa [activeOrderKey, a, x] using hkey_fst.symm
  have hkey_snd := congrArg Prod.snd hkey
  have hlower : lowerJetAt (j := j) a P = lowerJetAt (j := j) a P' := by
    dsimp [activeOrderKey] at hkey_snd
    rw [ha] at hkey_snd
    exact hkey_snd
  have hinit : ∀ k, k ≤ j →
      (hasseDerivative k P.1).eval a =
        (hasseDerivative k P'.1).eval a := by
    intro k hkj
    by_cases hk : k < j
    · exact congrFun hlower ⟨k, hk⟩
    · have hkeq : k = j := by omega
      subst k
      dsimp [activeOrderValue] at hvalue
      rw [ha] at hvalue
      exact hvalue
  have hspec := activeOrderChoice_spec hjr Q hweight P hP
  have hspec' := activeOrderChoice_spec hjr Q hweight P' hP'
  dsimp only [x, n, a] at hspec
  dsimp only [x, n'] at hspec'
  rw [ha] at hspec'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hz := firstNonzeroPartialHasseIndex_min x Q P'
        ⟨Q.degreeOf x, (mem_activeOrderSolutions x Q P').mp hP' |>.2⟩ hlt
    have heval := congrArg (fun S : Polynomial F => S.eval a) hz
    rw [eval_differentialSpecializationOver] at heval
    simp only [Polynomial.eval_zero] at heval
    have heq := eval_partialHasse_eq_of_initialJet a Q horder x n P P' hinit
    exact hspec.2.2.2 (by
      rw [eval_differentialSpecializationOver]
      simpa [n] using heq.trans heval)
  · have hz := firstNonzeroPartialHasseIndex_min x Q P
        ⟨Q.degreeOf x, (mem_activeOrderSolutions x Q P).mp hP |>.2⟩ hgt
    have heval := congrArg (fun S : Polynomial F => S.eval a) hz
    rw [eval_differentialSpecializationOver] at heval
    simp only [Polynomial.eval_zero] at heval
    have heq := eval_partialHasse_eq_of_initialJet a Q horder x n' P P' hinit
    exact hspec'.2.2.2 (by
      rw [eval_differentialSpecializationOver]
      simpa [n'] using heq.symm.trans heval)

/-- Within a fixed expansion-point/lower-jet key, the active Taylor value is
injective on the entire active-order branch, including all multiplicity
strata. -/
theorem activeOrderValue_injOn
    {q r D j t : ℕ} [CharP F q]
    (hq : q.Prime) (hjr : j ≤ r) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F r) (horder : HasJetOrderAtMost j Q)
    (hdegree : Q.degreeOf (jetAtOrder r j hjr) ≤ t) (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < Fintype.card F)
    (b : F × (Fin j → F)) :
    Set.InjOn (activeOrderValue (D := D) hjr Q)
      (↑((activeOrderSolutions D (jetAtOrder r j hjr) Q).filter
        (fun P => activeOrderKey hjr Q P = b)) : Set _) := by
  classical
  intro P hP P' hP' hvalue
  have hP_parts := Finset.mem_filter.mp hP
  have hP'_parts := Finset.mem_filter.mp hP'
  have hkey : activeOrderKey hjr Q P = activeOrderKey hjr Q P' :=
    hP_parts.2.trans hP'_parts.2.symm
  have hn_eq := firstNonzeroIndex_eq_of_key_value hjr Q horder hweight
    P P' hP_parts.1 hP'_parts.1 hkey hvalue
  let x := jetAtOrder r j hjr
  let n := firstNonzeroPartialHasseIndex x Q P
  let a := activeExpansionPoint x Q P
  have hkey_fst := congrArg Prod.fst hkey
  have ha : activeExpansionPoint x Q P' = a := by
    simpa [activeOrderKey, a, x] using hkey_fst.symm
  have hkey_snd := congrArg Prod.snd hkey
  have hlower : lowerJetAt (j := j) a P = lowerJetAt (j := j) a P' := by
    dsimp [activeOrderKey] at hkey_snd
    rw [ha] at hkey_snd
    exact hkey_snd
  have hinit : ∀ k, k ≤ j →
      (hasseDerivative k P.1).eval a =
        (hasseDerivative k P'.1).eval a := by
    intro k hkj
    by_cases hk : k < j
    · exact congrFun hlower ⟨k, hk⟩
    · have hkeq : k = j := by omega
      subst k
      dsimp [activeOrderValue] at hvalue
      rw [ha] at hvalue
      exact hvalue
  have hspec := activeOrderChoice_spec hjr Q hweight P hP_parts.1
  have hspec' := activeOrderChoice_spec hjr Q hweight P' hP'_parts.1
  dsimp only [x, n, a] at hspec
  dsimp only [x] at hspec'
  rw [← hn_eq, ha] at hspec'
  apply Subtype.ext
  apply regular_lift_unique_at_of_orderAtMost hq hjr hjD hDq a
      (partialHasse x (n - 1) Q) (horder.partialHasse x (n - 1)) P P'
  · exact degree_le_of_mem_degreeLT_succ P
  · exact degree_le_of_mem_degreeLT_succ P'
  · exact hspec.2.2.1
  · exact hspec'.2.2.1
  · have hnq : n < q :=
        hspec.2.1.trans_lt (hdegree.trans_lt htq)
    have hnpos : 0 < n := by simpa [n] using hspec.1
    rw [pderiv_partialHasse]
    have hnstep : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
    rw [hnstep, map_nsmul, nsmul_eq_mul]
    apply mul_ne_zero
    · exact (CharP.cast_eq_zero_iff F q n).not.mpr
        (Nat.not_dvd_of_pos_of_lt hnpos hnq)
    · rw [← eval_differentialSpecializationOver]
      exact hspec'.2.2.2
  · exact hinit

/- Evaluating a Hasse stratum in the fibre determined by an active-order
key agrees with differential specialization at the chosen expansion point. -/
set_option maxHeartbeats 800000 in
theorem fibrePolynomial_activeOrderKey_eval
    {r D j : ℕ} (hjr : j ≤ r)
    (Q : DifferentialPolynomialOver F r) (horder : HasJetOrderAtMost j Q)
    (P : Polynomial.degreeLT F (D + 1)) (b : F × (Fin j → F))
    (hkey : activeOrderKey hjr Q P = b) (m : ℕ) :
    (fibrePolynomial (jetAtOrder r j hjr)
      (lowerJetAssignmentAt hjr b.1 b.2) (partialHasse
        (jetAtOrder r j hjr) m Q)).eval (activeOrderValue hjr Q P) =
      (differentialSpecializationOver
        (partialHasse (jetAtOrder r j hjr) m Q) P).eval
          (activeExpansionPoint (jetAtOrder r j hjr) Q P) := by
  classical
  let x := jetAtOrder r j hjr
  let a := activeExpansionPoint x Q P
  have ha : a = b.1 := by
    simpa [activeOrderKey, a, x] using congrArg Prod.fst hkey
  have hlower : lowerJetAt (j := j) a P = b.2 := by
    simpa [activeOrderKey, a, x] using congrArg Prod.snd hkey
  have hlower_b : lowerJetAt (j := j) b.1 P = b.2 := by
    rw [← ha]
    exact hlower
  have hassignment : lowerJetAssignmentAt hjr b.1 b.2 =
      lowerJetAssignmentAt hjr a (lowerJetAt a P) := by
    rw [ha, hlower_b]
  rw [fibrePolynomial_eval, eval_differentialSpecializationOver]
  change MvPolynomial.eval
      (Function.update (lowerJetAssignmentAt hjr b.1 b.2) x
        ((hasseDerivative j P.1).eval a)) (partialHasse x m Q) =
    MvPolynomial.eval (differentialJet a P) (partialHasse x m Q)
  change MvPolynomial.eval₂Hom (RingHom.id F)
      (Function.update (lowerJetAssignmentAt hjr b.1 b.2) x
        ((hasseDerivative j P.1).eval a)) (partialHasse x m Q) =
    MvPolynomial.eval₂Hom (RingHom.id F)
      (differentialJet a P) (partialHasse x m Q)
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro v hv _
  have hvQ := partialHasse_vars_subset x m Q hv
  rcases v with (_ | i)
  · rw [hassignment]
    exact update_lowerJetAssignmentAt_jetAtOrder hjr a P none trivial
  · rw [hassignment]
    exact update_lowerJetAssignmentAt_jetAtOrder hjr a P (some i)
      (horder i hvQ)

/-- Fibre evaluation for a pair carrying an arbitrary nonvanishing expansion
point. -/
theorem fibrePolynomial_activePointKey_eval
    {r D j : ℕ} (hjr : j ≤ r)
    (Q : DifferentialPolynomialOver F r) (horder : HasJetOrderAtMost j Q)
    (z : ActivePointPair D (jetAtOrder r j hjr) Q)
    (b : F × (Fin j → F)) (hkey : activePointKey hjr Q z = b)
    (m : ℕ) :
    (fibrePolynomial (jetAtOrder r j hjr)
      (lowerJetAssignmentAt hjr b.1 b.2)
      (partialHasse (jetAtOrder r j hjr) m Q)).eval
        (activePointValue hjr Q z) =
      (differentialSpecializationOver
        (partialHasse (jetAtOrder r j hjr) m Q) z.1.1).eval z.2.1 := by
  classical
  let x := jetAtOrder r j hjr
  let a : F := z.2.1
  have ha : a = b.1 := by
    change z.2.1 = b.1
    exact congrArg Prod.fst hkey
  have hlower : lowerJetAt (j := j) a z.1.1 = b.2 := by
    change lowerJetAt (j := j) z.2.1 z.1.1 = b.2
    exact congrArg Prod.snd hkey
  have hassignment : lowerJetAssignmentAt hjr b.1 b.2 =
      lowerJetAssignmentAt hjr a (lowerJetAt a z.1.1) := by
    rw [← ha, ← hlower]
  rw [fibrePolynomial_eval, eval_differentialSpecializationOver]
  change MvPolynomial.eval
      (Function.update (lowerJetAssignmentAt hjr b.1 b.2) x
        ((hasseDerivative j z.1.1.1).eval a)) (partialHasse x m Q) =
    MvPolynomial.eval (differentialJet a z.1.1.1) (partialHasse x m Q)
  change MvPolynomial.eval₂Hom (RingHom.id F)
      (Function.update (lowerJetAssignmentAt hjr b.1 b.2) x
        ((hasseDerivative j z.1.1.1).eval a)) (partialHasse x m Q) =
    MvPolynomial.eval₂Hom (RingHom.id F)
      (differentialJet a z.1.1.1) (partialHasse x m Q)
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro v hv _
  have hvQ := partialHasse_vars_subset x m Q hv
  rcases v with (_ | i)
  · rw [hassignment]
    exact update_lowerJetAssignmentAt_jetAtOrder hjr a z.1.1.1 none trivial
  · rw [hassignment]
    exact update_lowerJetAssignmentAt_jetAtOrder hjr a z.1.1.1 (some i)
      (horder i hvQ)

set_option maxHeartbeats 1000000 in
/-- Every expansion-point/lower-jet fibre contains at most the active
coordinate degree many solution-point pairs. -/
theorem card_activePointPair_fibre_le
    {q r D j t : ℕ} [CharP F q]
    (hq : q.Prime) (hjr : j ≤ r) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F r) (horder : HasJetOrderAtMost j Q)
    (hdegree : Q.degreeOf (jetAtOrder r j hjr) ≤ t) (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < Fintype.card F)
    (b : F × (Fin j → F)) :
    (Finset.univ.filter fun z :
      ActivePointPair D (jetAtOrder r j hjr) Q =>
        activePointKey hjr Q z = b).card ≤ t := by
  classical
  let x := jetAtOrder r j hjr
  let s := Finset.univ.filter fun z :
      ActivePointPair D (jetAtOrder r j hjr) Q =>
    activePointKey hjr Q z = b
  let p := fibrePolynomial x (lowerJetAssignmentAt hjr b.1 b.2) Q
  by_cases hs : s.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hs
    have hz₀key := (Finset.mem_filter.mp hz₀).2
    have hchoice := activePointPair_spec hjr Q hweight z₀
    let n := firstNonzeroPartialHasseIndex x Q z₀.1.1
    have hnonzeroEval : (hasseDerivative n p).eval
        (activePointValue hjr Q z₀) ≠ 0 := by
      rw [← fibrePolynomial_partialHasse]
      rw [fibrePolynomial_activePointKey_eval hjr Q horder z₀ b hz₀key n]
      exact hchoice.2.2.2
    have hp_ne : p ≠ 0 := by
      intro hp
      rw [hp] at hnonzeroEval
      simp at hnonzeroEval
    let roots : Finset F := Finset.univ.filter fun v => p.eval v = 0
    have hmap : Set.MapsTo (activePointValue (D := D) hjr Q)
        (↑s : Set _) (↑roots : Set F) := by
      intro z hz
      have hzkey := (Finset.mem_filter.mp hz).2
      have hactive := (mem_activeOrderSolutions x Q z.1.1).mp z.1.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have heval := fibrePolynomial_activePointKey_eval
        hjr Q horder z b hzkey 0
      have hzero : differentialSpecializationOver
          (partialHasse x 0 Q) z.1.1 = 0 := by simpa using hactive.1
      simpa [p] using heval.trans (congrArg
        (fun S : Polynomial F => S.eval z.2.1) hzero)
    have hinj : Set.InjOn (activePointValue (D := D) hjr Q) (↑s : Set _) := by
      simpa [s] using
        (activePointValue_injOn hq hjr hjD hDq Q horder hdegree htq hweight b)
    calc
      (Finset.univ.filter fun z : ActivePointPair D x Q =>
          activePointKey hjr Q z = b).card = s.card := rfl
      _ ≤ roots.card := Finset.card_le_card_of_injOn _ hmap hinj
      _ ≤ p.natDegree := card_filter_eval_eq_zero_le_natDegree p hp_ne
      _ ≤ Q.degreeOf x := fibrePolynomial_natDegree_le_degreeOf x
        (lowerJetAssignmentAt hjr b.1 b.2) Q
      _ ≤ t := hdegree
  · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change s.card ≤ t
    simp [hsempty]

/-- The total number of active solution/nonvanishing-point pairs is bounded
by the same key space as before; amortization comes from the number of points
attached to each solution. -/
theorem card_activePointPair_le
    {q r D j t : ℕ} [CharP F q]
    (hq : q.Prime) (hjr : j ≤ r) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F r) (horder : HasJetOrderAtMost j Q)
    (hdegree : Q.degreeOf (jetAtOrder r j hjr) ≤ t) (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < Fintype.card F) :
    Fintype.card (ActivePointPair D (jetAtOrder r j hjr) Q) ≤
      t * Fintype.card F ^ (j + 1) := by
  classical
  calc
    Fintype.card (ActivePointPair D (jetAtOrder r j hjr) Q) =
        (Finset.univ : Finset
          (ActivePointPair D (jetAtOrder r j hjr) Q)).card := by simp
    _ ≤ t * Fintype.card (F × (Fin j → F)) := by
      apply card_le_mul_card_of_fibers
        (Finset.univ : Finset
          (ActivePointPair D (jetAtOrder r j hjr) Q))
        (activePointKey hjr Q) t
      intro b
      exact card_activePointPair_fibre_le hq hjr hjD hDq Q horder
        hdegree htq hweight b
    _ = t * Fintype.card F ^ (j + 1) := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        Nat.pow_succ]
      ac_rfl

/-- Amortized active-order count.  Every active solution contributes at
least `|F|-Delta` expansion points, while every point/lower-jet key supports
at most `t` solutions. -/
theorem card_sub_mul_activeOrderSolutions_le
    {q r D j t Delta : ℕ} [CharP F q]
    (hq : q.Prime) (hjr : j ≤ r) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F r) (horder : HasJetOrderAtMost j Q)
    (hdegree : Q.degreeOf (jetAtOrder r j hjr) ≤ t) (htq : t < q)
    (hDelta : Q.weightedTotalDegree (jetWeight (r := r) D) ≤ Delta)
    (hDeltaCard : Delta < Fintype.card F) :
    (Fintype.card F - Delta) *
        (activeOrderSolutions D (jetAtOrder r j hjr) Q).card ≤
      t * Fintype.card F ^ (j + 1) := by
  calc
    (Fintype.card F - Delta) *
        (activeOrderSolutions D (jetAtOrder r j hjr) Q).card =
      (activeOrderSolutions D (jetAtOrder r j hjr) Q).card *
        (Fintype.card F - Delta) := Nat.mul_comm _ _
    _ ≤ Fintype.card
        (ActivePointPair D (jetAtOrder r j hjr) Q) :=
      activeOrder_card_mul_card_sub_le_activePointPair hjr Q hDelta
    _ ≤ t * Fintype.card F ^ (j + 1) :=
      card_activePointPair_le hq hjr hjD hDq Q horder hdegree htq
        (hDelta.trans_lt hDeltaCard)

/-- Each fixed active-order key contains at most the active coordinate
degree many solutions.  The root polynomial is the original fibre; the
least nonzero Hasse stratum certifies that this fibre is nonzero. -/
theorem card_activeOrderSolutions_fibre_le
    {q r D j t : ℕ} [CharP F q]
    (hq : q.Prime) (hjr : j ≤ r) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F r) (horder : HasJetOrderAtMost j Q)
    (hdegree : Q.degreeOf (jetAtOrder r j hjr) ≤ t) (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < Fintype.card F)
    (b : F × (Fin j → F)) :
    ((activeOrderSolutions D (jetAtOrder r j hjr) Q).filter
      (fun P => activeOrderKey hjr Q P = b)).card ≤ t := by
  classical
  let x := jetAtOrder r j hjr
  let s := (activeOrderSolutions D x Q).filter
    (fun P => activeOrderKey hjr Q P = b)
  let p := fibrePolynomial x (lowerJetAssignmentAt hjr b.1 b.2) Q
  by_cases hs : s.Nonempty
  · obtain ⟨P₀, hP₀⟩ := hs
    have hP₀_parts := Finset.mem_filter.mp hP₀
    have hchoice := activeOrderChoice_spec hjr Q hweight P₀ hP₀_parts.1
    let n := firstNonzeroPartialHasseIndex x Q P₀
    have hnonzeroEval : (hasseDerivative n p).eval
        (activeOrderValue hjr Q P₀) ≠ 0 := by
      rw [← fibrePolynomial_partialHasse]
      rw [fibrePolynomial_activeOrderKey_eval hjr Q horder P₀ b
        hP₀_parts.2 n]
      exact hchoice.2.2.2
    have hp_ne : p ≠ 0 := by
      intro hp
      rw [hp] at hnonzeroEval
      simp at hnonzeroEval
    let roots : Finset F := Finset.univ.filter fun z => p.eval z = 0
    have hmap : Set.MapsTo (activeOrderValue (D := D) hjr Q)
        (↑s : Set _) (↑roots : Set F) := by
      intro P hP
      have hparts := Finset.mem_filter.mp hP
      have hactive := (mem_activeOrderSolutions x Q P).mp hparts.1
      change activeOrderValue hjr Q P ∈ roots
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have heval := fibrePolynomial_activeOrderKey_eval hjr Q horder P b
        hparts.2 0
      have hzero : differentialSpecializationOver
          (partialHasse x 0 Q) P = 0 := by simpa using hactive.1
      simpa [p] using heval.trans (congrArg (fun S : Polynomial F =>
        S.eval (activeExpansionPoint x Q P)) hzero)
    have hinj : Set.InjOn (activeOrderValue (D := D) hjr Q) (↑s : Set _) :=
      activeOrderValue_injOn hq hjr hjD hDq Q horder hdegree htq hweight b
    calc
      ((activeOrderSolutions D x Q).filter
          (fun P => activeOrderKey hjr Q P = b)).card = s.card := rfl
      _ ≤ roots.card := Finset.card_le_card_of_injOn _ hmap hinj
      _ ≤ p.natDegree := card_filter_eval_eq_zero_le_natDegree p hp_ne
      _ ≤ Q.degreeOf x := fibrePolynomial_natDegree_le_degreeOf x
        (lowerJetAssignmentAt hjr b.1 b.2) Q
      _ ≤ t := hdegree
  · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change s.card ≤ t
    simp [hsempty]

/-- The entire branch handled at active order `j` costs one expansion point,
`j` lower Taylor values, and at most `t` roots of the active fibre. -/
theorem card_activeOrderSolutions_le
    {q r D j t : ℕ} [CharP F q]
    (hq : q.Prime) (hjr : j ≤ r) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F r) (horder : HasJetOrderAtMost j Q)
    (hdegree : Q.degreeOf (jetAtOrder r j hjr) ≤ t) (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < Fintype.card F) :
    (activeOrderSolutions D (jetAtOrder r j hjr) Q).card ≤
      t * Fintype.card F ^ (j + 1) := by
  classical
  letI : Fintype (Polynomial.degreeLT F (D + 1)) :=
    Fintype.ofEquiv (Fin (D + 1) → F)
      (Polynomial.degreeLTEquiv F (D + 1)).toEquiv.symm
  calc
    (activeOrderSolutions D (jetAtOrder r j hjr) Q).card ≤
        t * Fintype.card (F × (Fin j → F)) := by
      apply card_le_mul_card_of_fibers
        (activeOrderSolutions D (jetAtOrder r j hjr) Q)
        (activeOrderKey hjr Q) t
      intro b
      exact card_activeOrderSolutions_fibre_le hq hjr hjD hDq Q horder
        hdegree htq hweight b
    _ = t * Fintype.card F ^ (j + 1) := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        Nat.pow_succ]
      ac_rfl

/-- A nonzero differential polynomial containing no jet variables cannot
specialize to the zero polynomial.  Re-embedding the independent variable
recovers the original multivariate polynomial on its support. -/
theorem differentialSpecializationOver_ne_zero_of_noJet
    {r : ℕ} (Q : DifferentialPolynomialOver F r) (hQ : Q ≠ 0)
    (hnoJet : ∀ i : Fin (r + 1), some i ∉ Q.vars)
    (P : Polynomial F) : differentialSpecializationOver Q P ≠ 0 := by
  classical
  intro hzero
  let reembed : Polynomial F →+* DifferentialPolynomialOver F r :=
    Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X none)
  have hrecover : reembed (differentialSpecializationOver Q P) = Q := by
    rw [differentialSpecializationOver, MvPolynomial.map_eval₂Hom]
    have hC : reembed.comp Polynomial.C = MvPolynomial.C := by
      ext c
      simp [reembed]
    rw [hC]
    calc
      MvPolynomial.eval₂Hom MvPolynomial.C
          (fun v : JetVariable r => reembed (match v with
            | none => Polynomial.X
            | some i => hasseDerivative (i : ℕ) P)) Q =
        MvPolynomial.eval₂Hom MvPolynomial.C MvPolynomial.X Q := by
          apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
          intro v hv _
          rcases v with (_ | i)
          · simp [reembed]
          · exact (hnoJet i hv).elim
      _ = Q := by simp
  rw [hzero, map_zero] at hrecover
  exact hQ hrecover.symm

/-- Every solution is either handled at the current active order or remains
a solution after extracting the top Hasse coefficient. -/
theorem card_differentialSolutionsOver_le_active_add_top
    {r D : ℕ} (x : JetVariable r) (Q : DifferentialPolynomialOver F r) :
    (differentialSolutionsOver D Q).card ≤
      (activeOrderSolutions D x Q).card +
        (differentialSolutionsOver D
          (partialHasse x (Q.degreeOf x) Q)).card := by
  classical
  let s := differentialSolutionsOver D Q
  let active := activeOrderSolutions D x Q
  let top := differentialSolutionsOver D
    (partialHasse x (Q.degreeOf x) Q)
  have hsubset : s ⊆ active ∪ top := by
    intro P hP
    have hsolution := (mem_differentialSolutionsOver Q P).mp hP
    by_cases htop : differentialSpecializationOver
        (partialHasse x (Q.degreeOf x) Q) P ≠ 0
    · apply Finset.mem_union_left top
      exact (mem_activeOrderSolutions x Q P).mpr ⟨hsolution, htop⟩
    · apply Finset.mem_union_right active
      apply (mem_differentialSolutionsOver _ P).mpr
      exact not_ne_iff.mp htop
  calc
    (differentialSolutionsOver D Q).card = s.card := rfl
    _ ≤ (active ∪ top).card := Finset.card_le_card hsubset
    _ ≤ active.card + top.card := Finset.card_union_le active top

/-- Internal root count over an arbitrary finite field of characteristic
`q`, for equations whose active jet order is at most `j`. -/
theorem card_differentialSolutionsOver_le_activeOrderSum
    {q r D j t : ℕ} [CharP F q]
    (hq : q.Prime) (hjr : j ≤ r) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F r) (hQ : Q ≠ 0)
    (horder : HasJetOrderAtMost j Q)
    (hcoord : ∀ i : Fin (r + 1), Q.degreeOf (some i) ≤ t)
    (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < Fintype.card F) :
    (differentialSolutionsOver D Q).card ≤
      t * ∑ k ∈ Finset.range (j + 1), Fintype.card F ^ (k + 1) := by
  classical
  induction j using Nat.strong_induction_on generalizing Q with
  | h j ih =>
      let x := jetAtOrder r j hjr
      let Qtop := partialHasse x (Q.degreeOf x) Q
      have hactive := card_activeOrderSolutions_le hq hjr hjD hDq Q horder
        (hcoord ⟨j, Nat.lt_succ_of_le hjr⟩) htq hweight
      have hsplit := card_differentialSolutionsOver_le_active_add_top
        (D := D) x Q
      by_cases hj : j = 0
      · subst j
        have htop_ne : Qtop ≠ 0 := partialHasse_top_ne_zero x Q hQ
        have hnoJet : ∀ i : Fin (r + 1), some i ∉ Qtop.vars := by
          simpa [Qtop, x] using horder.top_zero_noJet
        have htop_empty : differentialSolutionsOver D Qtop = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hne
          obtain ⟨P, hP⟩ := hne
          have hz := (mem_differentialSolutionsOver Qtop P).mp hP
          exact (differentialSpecializationOver_ne_zero_of_noJet
            Qtop htop_ne hnoJet P) hz
        have htop_card : (differentialSolutionsOver D Qtop).card = 0 := by
          rw [htop_empty]
          simp
        have hsplit' : (differentialSolutionsOver D Q).card ≤
            (activeOrderSolutions D x Q).card := by
          exact hsplit.trans_eq (by rw [htop_card, Nat.add_zero])
        exact hsplit'.trans (by simpa using hactive)
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        have hj'r : j' ≤ r := by omega
        have hj'D : j' ≤ D := by omega
        have htop_ne : Qtop ≠ 0 := partialHasse_top_ne_zero x Q hQ
        have htop_order : HasJetOrderAtMost j' Qtop := by
          simpa [Qtop, x] using horder.top_succ hjr
        have htop_coord : ∀ i : Fin (r + 1), Qtop.degreeOf (some i) ≤ t := by
          intro i
          exact (partialHasse_degreeOf_le x (Q.degreeOf x) Q (some i)).trans
            (hcoord i)
        have htop_weight : Qtop.weightedTotalDegree
            (jetWeight (r := r) D) < Fintype.card F :=
          (weightedTotalDegree_partialHasse_le
            (jetWeight (r := r) D) x (Q.degreeOf x) Q).trans_lt hweight
        have hrecursive := ih j' (Nat.lt_succ_self j') hj'r hj'D Qtop
          htop_ne htop_order htop_coord htop_weight
        calc
          (differentialSolutionsOver D Q).card ≤
              (activeOrderSolutions D x Q).card +
                (differentialSolutionsOver D Qtop).card := hsplit
          _ ≤ t * Fintype.card F ^ (j' + 1 + 1) +
                t * ∑ k ∈ Finset.range (j' + 1),
                  Fintype.card F ^ (k + 1) := Nat.add_le_add hactive hrecursive
          _ = t * (∑ k ∈ Finset.range (j' + 1),
                Fintype.card F ^ (k + 1) +
              Fintype.card F ^ (j' + 1 + 1)) := by
                rw [Nat.mul_add]
                ac_rfl
          _ = t * ∑ k ∈ Finset.range (j' + 1 + 1),
              Fintype.card F ^ (k + 1) := by
              congr 1
              symm
              rw [Finset.sum_range_succ]

/-- Expansion-point-amortized root count over an arbitrary finite field.
The same recursive partition is double-counted over every point where the
relevant separant stratum is nonzero. -/
theorem card_sub_mul_differentialSolutionsOver_le_activeOrderSum
    {q r D j t Delta : ℕ} [CharP F q]
    (hq : q.Prime) (hjr : j ≤ r) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F r) (hQ : Q ≠ 0)
    (horder : HasJetOrderAtMost j Q)
    (hcoord : ∀ i : Fin (r + 1), Q.degreeOf (some i) ≤ t)
    (htq : t < q)
    (hDelta : Q.weightedTotalDegree (jetWeight (r := r) D) ≤ Delta)
    (hDeltaCard : Delta < Fintype.card F) :
    (Fintype.card F - Delta) *
        (differentialSolutionsOver D Q).card ≤
      t * ∑ k ∈ Finset.range (j + 1), Fintype.card F ^ (k + 1) := by
  classical
  induction j using Nat.strong_induction_on generalizing Q with
  | h j ih =>
      let x := jetAtOrder r j hjr
      let Qtop := partialHasse x (Q.degreeOf x) Q
      have hactive := card_sub_mul_activeOrderSolutions_le
        hq hjr hjD hDq Q horder
          (hcoord ⟨j, Nat.lt_succ_of_le hjr⟩) htq hDelta hDeltaCard
      have hsplit := card_differentialSolutionsOver_le_active_add_top
        (D := D) x Q
      by_cases hj : j = 0
      · subst j
        have htop_ne : Qtop ≠ 0 := partialHasse_top_ne_zero x Q hQ
        have hnoJet : ∀ i : Fin (r + 1), some i ∉ Qtop.vars := by
          simpa [Qtop, x] using horder.top_zero_noJet
        have htop_empty : differentialSolutionsOver D Qtop = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hne
          obtain ⟨P, hP⟩ := hne
          have hz := (mem_differentialSolutionsOver Qtop P).mp hP
          exact (differentialSpecializationOver_ne_zero_of_noJet
            Qtop htop_ne hnoJet P) hz
        have hsplit' : (differentialSolutionsOver D Q).card ≤
            (activeOrderSolutions D x Q).card := by
          have htop_card : (differentialSolutionsOver D Qtop).card = 0 := by
            rw [htop_empty]
            simp
          exact hsplit.trans_eq (by rw [htop_card, Nat.add_zero])
        exact (Nat.mul_le_mul_left _ hsplit').trans (by simpa using hactive)
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        have hj'r : j' ≤ r := by omega
        have hj'D : j' ≤ D := by omega
        have htop_ne : Qtop ≠ 0 := partialHasse_top_ne_zero x Q hQ
        have htop_order : HasJetOrderAtMost j' Qtop := by
          simpa [Qtop, x] using horder.top_succ hjr
        have htop_coord : ∀ i : Fin (r + 1), Qtop.degreeOf (some i) ≤ t := by
          intro i
          exact (partialHasse_degreeOf_le x (Q.degreeOf x) Q (some i)).trans
            (hcoord i)
        have htop_Delta : Qtop.weightedTotalDegree
            (jetWeight (r := r) D) ≤ Delta :=
          (weightedTotalDegree_partialHasse_le
            (jetWeight (r := r) D) x (Q.degreeOf x) Q).trans hDelta
        have hrecursive := ih j' (Nat.lt_succ_self j') hj'r hj'D Qtop
          htop_ne htop_order htop_coord htop_Delta
        calc
          (Fintype.card F - Delta) *
              (differentialSolutionsOver D Q).card ≤
            (Fintype.card F - Delta) *
              ((activeOrderSolutions D x Q).card +
                (differentialSolutionsOver D Qtop).card) :=
              Nat.mul_le_mul_left _ hsplit
          _ = (Fintype.card F - Delta) *
                (activeOrderSolutions D x Q).card +
              (Fintype.card F - Delta) *
                (differentialSolutionsOver D Qtop).card := Nat.mul_add _ _ _
          _ ≤ t * Fintype.card F ^ (j' + 1 + 1) +
                t * ∑ k ∈ Finset.range (j' + 1),
                  Fintype.card F ^ (k + 1) :=
              Nat.add_le_add hactive hrecursive
          _ = t * (∑ k ∈ Finset.range (j' + 1),
                Fintype.card F ^ (k + 1) +
              Fintype.card F ^ (j' + 1 + 1)) := by
                rw [Nat.mul_add]
                ac_rfl
          _ = t * ∑ k ∈ Finset.range (j' + 1 + 1),
              Fintype.card F ^ (k + 1) := by
              congr 1
              symm
              rw [Finset.sum_range_succ]

end ActiveOrderFibreCount

section RegularStratumCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A single regular order-`j` stratum has at most `t * |F|^j`
solutions at a fixed expansion point. -/
theorem card_regularSolutionsAtZero_le
    {q D j t : ℕ} [CharP F q]
    (hq : q.Prime) (hjD : j ≤ D) (hDq : D < q)
    (Q : DifferentialPolynomialOver F j)
    (hdegree : Q.degreeOf (lastJet j) ≤ t) :
    (regularSolutionsAtZero D Q).card ≤ t * Fintype.card F ^ j := by
  classical
  letI : Fintype (Polynomial.degreeLT F (D + 1)) :=
    Fintype.ofEquiv (Fin (D + 1) → F)
      (Polynomial.degreeLTEquiv F (D + 1)).toEquiv.symm
  calc
    (regularSolutionsAtZero D Q).card ≤
        t * Fintype.card (Fin j → F) := by
      apply card_le_mul_card_of_fibers
        (regularSolutionsAtZero D Q)
        (fun P : Polynomial.degreeLT F (D + 1) => lowerJet P.1) t
      intro b
      exact card_regularSolutionsAtZero_fibre_le
        hq hjD hDq Q hdegree b
    _ = t * Fintype.card F ^ j := by simp

end RegularStratumCount

section PrimeFieldEvaluator

variable {q r D : ℕ} [NeZero q]

/-- The legacy coefficient-vector evaluator and the generic
degree-bounded-polynomial evaluator enumerate exactly the same objects. -/
theorem differentialSolutions_card_eq_over (Q : DifferentialPolynomial q r) :
    (differentialSolutions (NeZero.ne q) D Q).card =
      (differentialSolutionsOver D Q).card := by
  classical
  apply Finset.card_bij'
      (fun p _ => (Polynomial.degreeLTEquiv (ZMod q) (D + 1)).symm p)
      (fun P _ => Polynomial.degreeLTEquiv (ZMod q) (D + 1) P)
  · intro p hp
    rw [mem_differentialSolutionsOver]
    simpa [differentialSolutions, differentialSpecialization,
      differentialSpecializationOver, messagePolynomial] using
      (Finset.mem_filter.mp hp).2
  · intro P hP
    rw [differentialSolutions, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [mem_differentialSolutionsOver] at hP
    simpa [differentialSpecialization, differentialSpecializationOver,
      messagePolynomial] using hP
  · intro p hp
    exact (Polynomial.degreeLTEquiv (ZMod q) (D + 1)).apply_symm_apply p
  · intro P hP
    exact (Polynomial.degreeLTEquiv (ZMod q) (D + 1)).symm_apply_apply P

end PrimeFieldEvaluator

section FinalCardinality

/-- Fully internal degree-below-characteristic root count.  Base-field
solutions embed injectively into Mathlib's degree-`e` Galois field, where the
active-order recursion gives the exact geometric factor. -/
theorem kopparty_degree_lt_characteristic_cardinality
    {q r D t e : ℕ}
    (hq : Nat.Prime q) (hrD : r ≤ D) (hDq : D < q)
    (ht : 0 < t) (he : 0 < e)
    (Q : DifferentialPolynomial q r) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (r + 1), Q.degreeOf (some j) ≤ t)
    (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) < q ^ e) :
    (differentialSolutions hq.ne_zero D Q).card ≤
      t * rootCountGeometricFactor q e r := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  letI : Fact q.Prime := ⟨hq⟩
  let E := RootExtension q e
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq E := Classical.decEq E
  let f : ZMod q →+* E := algebraMap (ZMod q) E
  have hf : Function.Injective f := rootExtension_algebraMap_injective
  let QE : DifferentialPolynomialOver E r := MvPolynomial.map f Q
  have hQE : QE ≠ 0 := mvPolynomial_map_ne_zero f hf hQ
  have hcard : Fintype.card E = q ^ e := rootExtension_fintypeCard he.ne'
  have hcoordE : ∀ j : Fin (r + 1), QE.degreeOf (some j) ≤ t := by
    intro j
    rw [degreeOf_map_of_injective f hf]
    exact hcoord j
  have hweightE : QE.weightedTotalDegree (jetWeight (r := r) D) <
      Fintype.card E := by
    rw [weightedTotalDegree_map_of_injective f hf, hcard]
    exact hweight
  have hext := card_differentialSolutionsOver_le_activeOrderSum
    (F := E) hq (le_refl r) hrD hDq QE hQE
      (hasJetOrderAtMost_ambient QE) hcoordE htq hweightE
  calc
    (differentialSolutions hq.ne_zero D Q).card =
        (differentialSolutionsOver D Q).card :=
      differentialSolutions_card_eq_over Q
    _ ≤ (differentialSolutionsOver D QE).card :=
      card_differentialSolutionsOver_le_map f hf Q
    _ ≤ t * ∑ k ∈ Finset.range (r + 1),
        Fintype.card E ^ (k + 1) := hext
    _ = t * rootCountGeometricFactor q e r := by
      simp only [hcard, rootCountGeometricFactor, pow_mul]

/-- Expansion-point-amortized public root count.  If `Delta` bounds the
weighted degree strictly below the extension-field cardinality, every
solution is regular at at least `q^e-Delta` expansion points. -/
theorem kopparty_degree_lt_characteristic_cardinality_amortized
    {q r D t e Delta : ℕ}
    (hq : Nat.Prime q) (hrD : r ≤ D) (hDq : D < q)
    (ht : 0 < t) (he : 0 < e)
    (Q : DifferentialPolynomial q r) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (r + 1), Q.degreeOf (some j) ≤ t)
    (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) ≤ Delta)
    (hDelta : Delta < q ^ e) :
    (q ^ e - Delta) * (differentialSolutions hq.ne_zero D Q).card ≤
      t * rootCountGeometricFactor q e r := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  letI : Fact q.Prime := ⟨hq⟩
  let E := RootExtension q e
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq E := Classical.decEq E
  let f : ZMod q →+* E := algebraMap (ZMod q) E
  have hf : Function.Injective f := rootExtension_algebraMap_injective
  let QE : DifferentialPolynomialOver E r := MvPolynomial.map f Q
  have hQE : QE ≠ 0 := mvPolynomial_map_ne_zero f hf hQ
  have hcard : Fintype.card E = q ^ e := rootExtension_fintypeCard he.ne'
  have hcoordE : ∀ j : Fin (r + 1), QE.degreeOf (some j) ≤ t := by
    intro j
    rw [degreeOf_map_of_injective f hf]
    exact hcoord j
  have hweightE : QE.weightedTotalDegree (jetWeight (r := r) D) ≤ Delta := by
    rw [weightedTotalDegree_map_of_injective f hf]
    exact hweight
  have hDeltaE : Delta < Fintype.card E := by simpa [hcard] using hDelta
  have hext := card_sub_mul_differentialSolutionsOver_le_activeOrderSum
    (F := E) hq (le_refl r) hrD hDq QE hQE
      (hasJetOrderAtMost_ambient QE) hcoordE htq hweightE hDeltaE
  calc
    (q ^ e - Delta) * (differentialSolutions hq.ne_zero D Q).card =
        (q ^ e - Delta) * (differentialSolutionsOver D Q).card := by
      rw [differentialSolutions_card_eq_over Q]
    _ ≤ (q ^ e - Delta) * (differentialSolutionsOver D QE).card :=
      Nat.mul_le_mul_left _ (card_differentialSolutionsOver_le_map f hf Q)
    _ = (Fintype.card E - Delta) *
        (differentialSolutionsOver D QE).card := by rw [hcard]
    _ ≤ t * ∑ k ∈ Finset.range (r + 1),
        Fintype.card E ^ (k + 1) := hext
    _ = t * rootCountGeometricFactor q e r := by
      simp only [hcard, rootCountGeometricFactor, pow_mul]

/-- Quotient form of the amortized bound, convenient for list-size
consumers. -/
theorem kopparty_degree_lt_characteristic_cardinality_div
    {q r D t e Delta : ℕ}
    (hq : Nat.Prime q) (hrD : r ≤ D) (hDq : D < q)
    (ht : 0 < t) (he : 0 < e)
    (Q : DifferentialPolynomial q r) (hQ : Q ≠ 0)
    (hcoord : ∀ j : Fin (r + 1), Q.degreeOf (some j) ≤ t)
    (htq : t < q)
    (hweight : Q.weightedTotalDegree (jetWeight (r := r) D) ≤ Delta)
    (hDelta : Delta < q ^ e) :
    (differentialSolutions hq.ne_zero D Q).card ≤
      (t * rootCountGeometricFactor q e r) / (q ^ e - Delta) := by
  apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hDelta)).2
  rw [Nat.mul_comm]
  exact kopparty_degree_lt_characteristic_cardinality_amortized
    hq hrD hDq ht he Q hQ hcoord htq hweight hDelta

end FinalCardinality

end RSListDecoding
