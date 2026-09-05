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

/-- The highest jet variable in an order-`j` equation. -/
def lastJet (j : ℕ) : JetVariable j := some ⟨j, by omega⟩

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

/-- View a multivariate polynomial as a univariate polynomial in `x`, after
fixing every other variable. -/
def fibrePolynomial (x : σ) (a : σ → F) (Q : MvPolynomial σ F) :
    Polynomial F :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun v => if v = x then Polynomial.X else Polynomial.C (a v)) Q

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

end RSListDecoding
