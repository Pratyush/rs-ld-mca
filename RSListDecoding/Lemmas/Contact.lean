import RSListDecoding.Defs.LocalConstraints
import RSListDecoding.Lemmas.HiddenRemainder

/-!
# Local contact implies high-order divisibility

This module proves the contact lemma from the manuscript.  The main algebraic
lemma is deliberately more general than the Reed--Solomon application: if all
monomials of contact order below `m` have zero coefficient, then every
specialization sending `T` to `t` and `E` to a multiple of `t^d` is divisible
by `t^m`.  Visible jet variables may be specialized arbitrarily.
-/

noncomputable section

open scoped BigOperators

namespace RSListDecoding

open MvPolynomial Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]
variable {d m : ℕ}

/-- A monomial of contact order `w` acquires a factor `t^w` whenever `T` is
sent to `t` and `E` is sent to a multiple of `t^d`. -/
theorem contactOrder_pow_dvd_monomialSpecialization
    (f : R →+* S) (g : LocalVariable d → S) (t : S)
    (hT : g (localT d) = t)
    (hE : t ^ d ∣ g (localE d))
    (e : LocalVariable d →₀ ℕ) :
    t ^ contactOrder d e ∣
      f (1 : R) * e.prod fun v exponent => g v ^ exponent := by
  have hprod :
      (∏ v ∈ e.support, t ^ (contactWeight d v * e v)) ∣
        ∏ v ∈ e.support, g v ^ e v := by
    apply Finset.prod_dvd_prod_of_dvd
    intro v hv
    rcases v with (_ | (_ | j))
    · have hT' : g none = t := by simpa [localT] using hT
      rw [hT']
      simp [contactWeight]
    · simpa [contactWeight, localE, pow_mul] using
        (pow_dvd_pow_of_dvd hE (e (some none)))
    · simp [contactWeight]
  simpa [contactOrder, Finsupp.sum, Finsupp.prod,
    Finset.prod_pow_eq_pow_sum] using hprod

/-- Coefficient-form contact constraints imply high-order divisibility under
every substitution respecting the contact orders of `T` and `E`. -/
theorem pow_dvd_eval₂Hom_of_lowContact_coeff_zero
    (F : LocalPolynomial R d)
    (hcoeff : ∀ e, contactOrder d e < m → MvPolynomial.coeff e F = 0)
    (f : R →+* S) (g : LocalVariable d → S) (t : S)
    (hT : g (localT d) = t)
    (hE : t ^ d ∣ g (localE d)) :
    t ^ m ∣ MvPolynomial.eval₂Hom f g F := by
  rw [F.as_sum, map_sum]
  apply Finset.dvd_sum
  intro e he
  rw [MvPolynomial.eval₂Hom_monomial]
  have hne : MvPolynomial.coeff e F ≠ 0 := MvPolynomial.mem_support_iff.mp he
  have hm : m ≤ contactOrder d e := by
    by_contra h
    exact hne (hcoeff e (Nat.lt_of_not_ge h))
  refine (pow_dvd_pow t hm).trans ?_
  simpa [mul_assoc] using
    ((contactOrder_pow_dvd_monomialSpecialization f g t hT hE e).mul_left
      (f (MvPolynomial.coeff e F)))

/-- Unbundled coefficient consequence of the local constraint map. -/
theorem coeff_contactTranslate_eq_zero_of_satisfiesLocalConstraints
    (Q : MvPolynomial (JetVariable d) R) (alpha y : R)
    (hQ : SatisfiesLocalConstraints m alpha y Q)
    (e : LocalVariable d →₀ ℕ) (he : contactOrder d e < m) :
    MvPolynomial.coeff e (contactTranslate alpha y Q) = 0 := by
  have h := congrFun hQ (⟨e, he⟩ : LowContactIndex d m)
  change MvPolynomial.coeff e (contactTranslate alpha y Q) = (0 : R) at h
  exact h

/-- The local constraints imply `X^m` divisibility after substituting an
arbitrary hidden remainder divisible by `X^d` and arbitrary visible jets. -/
theorem X_pow_dvd_contactEvaluation_of_satisfiesLocalConstraints
    (Q : MvPolynomial (JetVariable d) R) (alpha y : R)
    (hQ : SatisfiesLocalConstraints m alpha y Q)
    (E : Polynomial R) (hE : Polynomial.X ^ d ∣ E)
    (jets : Fin d → Polynomial R) :
    Polynomial.X ^ m ∣
      MvPolynomial.eval₂Hom Polynomial.C
        (fun v : LocalVariable d =>
          match v with
          | none => Polynomial.X
          | some none => E
          | some (some j) => jets j)
        (contactTranslate alpha y Q) := by
  apply pow_dvd_eval₂Hom_of_lowContact_coeff_zero
    (F := contactTranslate alpha y Q)
    (fun e he => coeff_contactTranslate_eq_zero_of_satisfiesLocalConstraints
      Q alpha y hQ e he)
    Polynomial.C _ Polynomial.X
  · rfl
  · exact hE

/-- Evaluating the two-step local change of variables at the hidden Taylor
remainder recovers the ordinary shifted differential specialization. -/
theorem eval₂Hom_contactTranslate_hiddenTaylor
    (Q : MvPolynomial (JetVariable d) R) (P : Polynomial R) (alpha y : R)
    (hy : P.eval alpha = y) :
    MvPolynomial.eval₂Hom Polynomial.C
        (fun v : LocalVariable d =>
          match v with
          | none => Polynomial.X
          | some none => hiddenTaylorRemainder d P alpha
          | some (some j) =>
              (hasseDerivative ((j : ℕ) + 1) P).comp
                (Polynomial.C alpha + Polynomial.X))
        (contactTranslate alpha y Q) =
      MvPolynomial.eval₂Hom Polynomial.C
        (fun v : JetVariable d =>
          match v with
          | none => Polynomial.C alpha + Polynomial.X
          | some j =>
              (hasseDerivative (j : ℕ) P).comp
                (Polynomial.C alpha + Polynomial.X)) Q := by
  simp only [contactTranslate, AlgHom.comp_apply, rewriteUToE, translateToU,
    MvPolynomial.eval₂Hom_bind₁]
  apply MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext v
  rcases v with (_ | j)
  · simp [localT]
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cases_zero, Fin.val_zero, hasseDerivative,
        Polynomial.hasseDeriv_zero']
      simp only [map_add, map_mul, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', localT, localU, localE]
      have hJet :
          MvPolynomial.eval₂Hom Polynomial.C
              (fun v : LocalVariable d =>
                match v with
                | none => Polynomial.X
                | some none => hiddenTaylorRemainder d P alpha
                | some (some j) =>
                    (hasseDerivative ((j : ℕ) + 1) P).comp
                      (Polynomial.C alpha + Polynomial.X))
              localJetSum =
            ∑ j : Fin d,
              Polynomial.C ((-1 : R) ^ ((j : ℕ) + 2)) *
                Polynomial.X ^ (j : ℕ) *
                  (hasseDerivative ((j : ℕ) + 1) P).comp
                    (Polynomial.C alpha + Polynomial.X) := by
        simp [localJetSum, localJetTerm, localT, localY]
      rw [hJet]
      have hReindex :
          Polynomial.X *
              (∑ j : Fin d,
                Polynomial.C ((-1 : R) ^ ((j : ℕ) + 2)) *
                  Polynomial.X ^ (j : ℕ) *
                    (hasseDerivative ((j : ℕ) + 1) P).comp
                      (Polynomial.C alpha + Polynomial.X)) =
            ∑ ell ∈ Finset.Ico 1 (d + 1),
              Polynomial.C ((-1 : R) ^ (ell + 1)) * Polynomial.X ^ ell *
                (hasseDerivative ell P).comp
                  (Polynomial.C alpha + Polynomial.X) := by
        let term : ℕ → Polynomial R := fun j =>
          Polynomial.C ((-1 : R) ^ (j + 2)) * Polynomial.X ^ j *
            (hasseDerivative (j + 1) P).comp
              (Polynomial.C alpha + Polynomial.X)
        change Polynomial.X * (∑ j : Fin d, term (j : ℕ)) = _
        rw [Fin.sum_univ_eq_sum_range term d, Finset.sum_Ico_eq_sum_range,
          show d + 1 - 1 = d by omega, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [term]
        simp only [Nat.one_add, pow_succ']
        ring
      rw [mul_add, hReindex]
      calc
        Polynomial.C y +
              (Polynomial.X * hiddenTaylorRemainder d P alpha +
                ∑ ell ∈ Finset.Ico 1 (d + 1),
                  Polynomial.C ((-1 : R) ^ (ell + 1)) * Polynomial.X ^ ell *
                    (hasseDerivative ell P).comp
                      (Polynomial.C alpha + Polynomial.X)) =
            Polynomial.C (P.eval alpha) +
              ∑ ell ∈ Finset.Ico 1 (d + 1),
                Polynomial.C ((-1 : R) ^ (ell + 1)) * Polynomial.X ^ ell *
                  (hasseDerivative ell P).comp
                    (Polynomial.C alpha + Polynomial.X) +
                Polynomial.X * hiddenTaylorRemainder d P alpha := by
                  rw [hy]
                  ring
        _ = P.comp (Polynomial.C alpha + Polynomial.X) :=
          (hiddenTaylor_identity_signed d P alpha).symm
    · simp [localY]

/-- `lem:contact` in the manuscript, in its exact shifted polynomial
coordinates. -/
theorem X_pow_dvd_shiftedDifferentialSpecialization_of_contact
    (Q : MvPolynomial (JetVariable d) R) (P : Polynomial R) (alpha y : R)
    (hy : P.eval alpha = y)
    (hQ : SatisfiesLocalConstraints m alpha y Q) :
    Polynomial.X ^ m ∣
      MvPolynomial.eval₂Hom Polynomial.C
        (fun v : JetVariable d =>
          match v with
          | none => Polynomial.C alpha + Polynomial.X
          | some j =>
              (hasseDerivative (j : ℕ) P).comp
                (Polynomial.C alpha + Polynomial.X)) Q := by
  rw [← eval₂Hom_contactTranslate_hiddenTaylor Q P alpha y hy]
  exact X_pow_dvd_contactEvaluation_of_satisfiesLocalConstraints
    Q alpha y hQ (hiddenTaylorRemainder d P alpha)
      (X_pow_dvd_hiddenTaylorRemainder d P alpha)
      (fun j => (hasseDerivative ((j : ℕ) + 1) P).comp
        (Polynomial.C alpha + Polynomial.X))

/-- The shifted expression above is the translate of the repository's
canonical differential specialization. -/
theorem differentialSpecialization_comp_eq_shifted_eval₂Hom
    {q : ℕ} (Q : DifferentialPolynomial q d)
    (P : Polynomial (ZMod q)) (alpha : ZMod q) :
    (differentialSpecialization Q P).comp
        (Polynomial.C alpha + Polynomial.X) =
      MvPolynomial.eval₂Hom Polynomial.C
        (fun v : JetVariable d =>
          match v with
          | none => Polynomial.C alpha + Polynomial.X
          | some j =>
              (hasseDerivative (j : ℕ) P).comp
                (Polynomial.C alpha + Polynomial.X)) Q := by
  rw [differentialSpecialization]
  change Polynomial.compRingHom (Polynomial.C alpha + Polynomial.X)
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun v : JetVariable d =>
          match v with
          | none => Polynomial.X
          | some j => hasseDerivative (j : ℕ) P) Q) = _
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext r
    simp
  · funext v
    rcases v with (_ | j) <;> simp [Polynomial.coe_compRingHom_apply]
  · rfl

/-- Translate divisibility at the formal origin back to the usual linear
factor at `alpha`.  This is the algebraic bridge from the manuscript's
`T^m` congruence to root multiplicity. -/
theorem pow_X_sub_C_dvd_of_X_pow_dvd_comp_C_add_X
    (p : Polynomial R) (alpha : R)
    (h : Polynomial.X ^ m ∣
      p.comp (Polynomial.C alpha + Polynomial.X)) :
    (Polynomial.X - Polynomial.C alpha) ^ m ∣ p := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r.comp (Polynomial.X - Polynomial.C alpha), ?_⟩
  have hcomp := congrArg
    (fun s : Polynomial R =>
      s.comp (Polynomial.X - Polynomial.C alpha)) hr
  simpa [Polynomial.comp_assoc] using hcomp

/-- Contact in the canonical form used by the global specialization: after
translating the agreement point to the origin, the specialization is
divisible by `X^m`. -/
theorem X_pow_dvd_differentialSpecialization_comp_of_contact
    {q : ℕ} (Q : DifferentialPolynomial q d)
    (P : Polynomial (ZMod q)) (alpha y : ZMod q)
    (hy : P.eval alpha = y)
    (hQ : SatisfiesLocalConstraints m alpha y Q) :
    Polynomial.X ^ m ∣
      (differentialSpecialization Q P).comp
        (Polynomial.C alpha + Polynomial.X) := by
  rw [differentialSpecialization_comp_eq_shifted_eval₂Hom]
  exact X_pow_dvd_shiftedDifferentialSpecialization_of_contact
    Q P alpha y hy hQ

/-- Root-multiplicity form of the contact lemma, ready for the distinct-root
degree argument. -/
theorem pow_X_sub_C_dvd_differentialSpecialization_of_contact
    {q : ℕ} (Q : DifferentialPolynomial q d)
    (P : Polynomial (ZMod q)) (alpha y : ZMod q)
    (hy : P.eval alpha = y)
    (hQ : SatisfiesLocalConstraints m alpha y Q) :
    (Polynomial.X - Polynomial.C alpha) ^ m ∣
      differentialSpecialization Q P := by
  exact pow_X_sub_C_dvd_of_X_pow_dvd_comp_C_add_X
    (differentialSpecialization Q P) alpha
      (X_pow_dvd_differentialSpecialization_comp_of_contact
        Q P alpha y hy hQ)

end RSListDecoding
