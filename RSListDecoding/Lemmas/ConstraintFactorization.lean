import RSListDecoding.Defs.ConstraintMap
import RSListDecoding.Defs.InterpolationSpace

/-!
# Factorization of the global constraints through the local monomial spaces

This file supplies the support bookkeeping behind the local rank argument.
The proofs use additive weights on monomial exponents.  This avoids choosing
coordinates or coefficients and therefore works over an arbitrary
commutative coefficient ring up to the one statement involving the global
`ZMod` interpolation space.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace RSListDecoding

open MvPolynomial

/-! ## Support weights under substitution -/

section SupportWeights

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
variable {σ τ : Type*}

omit [PartialOrder M] [IsOrderedAddMonoid M] in
private theorem support_weight_C_eq_zero (w : τ → M) (a : R)
    {e : τ →₀ ℕ} (he : e ∈ (C a : MvPolynomial τ R).support) :
    Finsupp.weight w e = 0 := by
  classical
  have he' : e ∈ ({0} : Finset (τ →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset he
  have : e = 0 := Finset.mem_singleton.mp he'
  subst e
  exact map_zero (Finsupp.weight w)

omit [PartialOrder M] [IsOrderedAddMonoid M] in
private theorem support_weight_X_eq (w : τ → M) (i : τ)
    {e : τ →₀ ℕ} (he : e ∈ (X i : MvPolynomial τ R).support) :
    Finsupp.weight w e = w i := by
  classical
  have he' : e ∈ ({Finsupp.single i 1} : Finset (τ →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset he
  have : e = Finsupp.single i 1 := Finset.mem_singleton.mp he'
  subst e
  rw [Finsupp.weight_single]
  exact one_nsmul (w i)

omit [IsOrderedAddMonoid M] in
private theorem support_weight_add_le (w : τ → M)
    {P Q : MvPolynomial τ R} {a : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a)
    (hQ : ∀ e ∈ Q.support, Finsupp.weight w e ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (P + Q).support) :
    Finsupp.weight w e ≤ a := by
  classical
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with heP | heQ
  · exact hP e heP
  · exact hQ e heQ

omit [IsOrderedAddMonoid M] in
private theorem support_weight_sum_le (w : τ → M)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : ι → MvPolynomial τ R) {a : M}
    (hP : ∀ i ∈ s, ∀ e ∈ (P i).support, Finsupp.weight w e ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (s.sum P).support) :
    Finsupp.weight w e ≤ a := by
  classical
  have he' := MvPolynomial.support_sum he
  rcases Finset.mem_biUnion.mp he' with ⟨i, hi, hei⟩
  exact hP i hi e hei

private theorem support_weight_mul_le (w : τ → M)
    {P Q : MvPolynomial τ R} {a b : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a)
    (hQ : ∀ e ∈ Q.support, Finsupp.weight w e ≤ b)
    {e : τ →₀ ℕ} (he : e ∈ (P * Q).support) :
    Finsupp.weight w e ≤ a + b := by
  classical
  have he' : e ∈ P.support + Q.support := MvPolynomial.support_mul P Q he
  rcases Finset.mem_add.mp he' with ⟨eP, heP, eQ, heQ, rfl⟩
  simpa using add_le_add (hP eP heP) (hQ eQ heQ)

private theorem support_weight_pow_le (w : τ → M)
    {P : MvPolynomial τ R} {a : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a) (n : ℕ)
    {e : τ →₀ ℕ} (he : e ∈ (P ^ n).support) :
    Finsupp.weight w e ≤ n • a := by
  induction n generalizing e with
  | zero =>
      simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | succ n ih =>
      rw [pow_succ] at he
      simpa [succ_nsmul] using support_weight_mul_le w
        (fun e he => ih he) hP he

private theorem support_weight_prod_le (w : τ → M)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : ι → MvPolynomial τ R) (a : ι → M)
    (hP : ∀ i ∈ s, ∀ e ∈ (P i).support, Finsupp.weight w e ≤ a i)
    {e : τ →₀ ℕ} (he : e ∈ (s.prod P).support) :
    Finsupp.weight w e ≤ s.sum a := by
  classical
  induction s using Finset.induction_on generalizing e with
  | empty =>
      simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi] at he
      rw [Finset.sum_insert hi]
      exact support_weight_mul_le w
        (hP i (Finset.mem_insert_self i s))
        (fun e he => ih
          (fun j hj => hP j (Finset.mem_insert_of_mem hj)) he) he

/-- Substitution cannot increase a support weight if every substituted
variable has support weight at most the weight assigned to that variable. -/
private theorem support_weight_bind₁_le (wSource : σ → M) (wTarget : τ → M)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, ∀ e ∈ (f i).support,
      Finsupp.weight wTarget e ≤ wSource i)
    {P : MvPolynomial σ R} {a : M}
    (hP : ∀ u ∈ P.support, Finsupp.weight wSource u ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (MvPolynomial.bind₁ f P).support) :
    Finsupp.weight wTarget e ≤ a := by
  classical
  rw [MvPolynomial.as_sum P, map_sum] at he
  have he' := MvPolynomial.support_sum he
  rcases Finset.mem_biUnion.mp he' with ⟨u, hu, heu⟩
  rw [MvPolynomial.bind₁_monomial] at heu
  have hprod : ∀ v ∈ (u.support.prod fun i => f i ^ u i).support,
      Finsupp.weight wTarget v ≤ Finsupp.weight wSource u := by
    intro v hv
    simpa only [Finsupp.weight_apply, Finsupp.sum] using
      (support_weight_prod_le wTarget u.support
        (fun i => f i ^ u i) (fun i => u i • wSource i)
        (fun i hi v hv => support_weight_pow_le wTarget (hf i) (u i) hv) hv)
  have hmul := support_weight_mul_le wTarget
    (a := (0 : M)) (b := Finsupp.weight wSource u)
    (fun v hv => le_of_eq (support_weight_C_eq_zero wTarget _ hv))
    hprod heu
  have hmono : Finsupp.weight wTarget e ≤ Finsupp.weight wSource u := by
    simpa using hmul
  exact hmono.trans (hP u hu)

end SupportWeights

/-! ## The weights used by the two local coordinate changes -/

/-- Signed `U`-minus-`T` weight.  Nonpositive weight is the condition that
every occurrence of `U` is accompanied by an occurrence of `T`. -/
private def uMinusTWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => 1
  | some (some _) => 0

/-- Weight selecting the visible first jet `Y₁`. -/
private def visibleFirstWeight (d : ℕ) : LocalVariable d → ℕ
  | some (some j) => if (j : ℕ) = 0 then 1 else 0
  | _ => 0

/-- Anisotropic weight of the visible jets. -/
private def visibleAnisotropicWeight (d : ℕ) : LocalVariable d → ℕ
  | some (some j) => (j : ℕ)
  | _ => 0

/-- Weight that counts the visible first jet together with `U`. -/
private def firstPlusUWeight (d : ℕ) : LocalVariable d → ℕ
  | some none => 1
  | some (some j) => if (j : ℕ) = 0 then 1 else 0
  | none => 0

/-- Signed visible-first-jet minus `T` weight after rewriting. -/
private def firstMinusTWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => 0
  | some (some j) => if (j : ℕ) = 0 then 1 else 0

/-- The corresponding source weight: rewriting one `U` may create one
visible first jet, while retaining the `-T` contribution. -/
private def firstPlusUMinusTWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => 1
  | some (some j) => if (j : ℕ) = 0 then 1 else 0

/-- Signed weight `anisotropic weight - contact order` after the rewrite. -/
private def anisotropicMinusContactWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => -(d : ℤ)
  | some (some j) => (j : ℤ)

/-- The corresponding signed weight before the rewrite: `U` has weight zero. -/
private def anisotropicMinusTWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => 0
  | some (some j) => (j : ℤ)

/-- Signed `E`-minus-`T` weight after the contact rewrite. -/
private def eMinusTWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => 1
  | some (some _) => 0

/-- Negative contact order after the rewrite. -/
private def negContactWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => -(d : ℤ)
  | some (some _) => 0

/-- Negative `T`-degree before the rewrite. -/
private def negTWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | _ => 0

/-- Direct first-jet weight on the global `Option`-indexed variables. -/
private def globalFirstWeight (d : ℕ) : JetVariable d → ℕ
  | none => 0
  | some j => if (j : ℕ) = 1 then 1 else 0

/-- Direct higher-jet weight on the global `Option`-indexed variables. -/
private def globalHigherWeight (d : ℕ) : JetVariable d → ℕ
  | none => 0
  | some j => (j : ℕ) - 1

private theorem weight_uMinusTWeight {d : ℕ} (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (uMinusTWeight d) e =
      (e (localU d) : ℤ) - e (localT d) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_option, Fintype.sum_option]
  simp [uMinusTWeight, localU, localT]
  ring

private theorem weight_visibleFirstWeight {d : ℕ} (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (visibleFirstWeight d) e = localFirstJetExponent e := by
  classical
  rw [Finsupp.weight_apply, localFirstJetExponent,
    Finsupp.sum_fintype _ _ (by simp),
    Finsupp.sum_fintype _ _ (by
      intro i
      rcases i with (_ | (_ | j)) <;> simp)]
  apply Finset.sum_congr rfl
  intro v hv
  rcases v with (_ | (_ | j))
  · simp [visibleFirstWeight]
  · simp [visibleFirstWeight]
  · simp [visibleFirstWeight]

private theorem weight_visibleAnisotropicWeight {d : ℕ}
    (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (visibleAnisotropicWeight d) e =
      localAnisotropicWeight e := by
  classical
  rw [Finsupp.weight_apply, localAnisotropicWeight,
    Finsupp.sum_fintype _ _ (by simp),
    Finsupp.sum_fintype _ _ (by
      intro i
      rcases i with (_ | (_ | j)) <;> simp)]
  apply Finset.sum_congr rfl
  intro v hv
  rcases v with (_ | (_ | j))
  · simp [visibleAnisotropicWeight]
  · simp [visibleAnisotropicWeight]
  · simp [visibleAnisotropicWeight, Nat.mul_comm]

private theorem weight_firstPlusUWeight {d : ℕ} (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (firstPlusUWeight d) e =
      localFirstJetExponent e + e (localU d) := by
  classical
  rw [Finsupp.weight_apply, localFirstJetExponent,
    Finsupp.sum_fintype _ _ (by simp),
    Finsupp.sum_fintype _ _ (by
      intro i
      rcases i with (_ | (_ | j)) <;> simp)]
  simp_rw [Fintype.sum_option]
  simp only [firstPlusUWeight, localU, nsmul_eq_mul, mul_one, mul_zero,
    Nat.cast_id, zero_add]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : (j : ℕ) = 0 <;> simp [h]

private theorem weight_firstMinusTWeight {d : ℕ}
    (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (firstMinusTWeight d) e =
      (localFirstJetExponent e : ℤ) - e (localT d) := by
  classical
  rw [Finsupp.weight_apply, localFirstJetExponent,
    Finsupp.sum_fintype _ _ (by simp),
    Finsupp.sum_fintype _ _ (by
      intro i
      rcases i with (_ | (_ | j)) <;> simp)]
  simp_rw [Fintype.sum_option]
  simp [firstMinusTWeight, localT, sub_eq_add_neg, Nat.cast_sum]
  ring

private theorem weight_firstPlusUMinusTWeight {d : ℕ}
    (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (firstPlusUMinusTWeight d) e =
      (localFirstJetExponent e : ℤ) + e (localU d) - e (localT d) := by
  classical
  rw [Finsupp.weight_apply, localFirstJetExponent,
    Finsupp.sum_fintype _ _ (by simp),
    Finsupp.sum_fintype _ _ (by
      intro i
      rcases i with (_ | (_ | j)) <;> simp)]
  simp_rw [Fintype.sum_option]
  simp [firstPlusUMinusTWeight, localU, localT, sub_eq_add_neg,
    Nat.cast_sum]
  ring

private theorem weight_anisotropicMinusContactWeight {d : ℕ}
    (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (anisotropicMinusContactWeight d) e =
      (localAnisotropicWeight e : ℤ) - contactOrder d e := by
  classical
  rw [Finsupp.weight_apply, localAnisotropicWeight, contactOrder,
    Finsupp.sum_fintype _ _ (by simp),
    Finsupp.sum_fintype _ _ (by
      intro i
      rcases i with (_ | (_ | j)) <;> simp),
    Finsupp.sum_fintype _ _ (by simp)]
  simp_rw [Fintype.sum_option]
  simp [anisotropicMinusContactWeight, contactWeight, sub_eq_add_neg,
    Nat.cast_sum, Nat.cast_mul, mul_comm]
  ring

private theorem weight_anisotropicMinusTWeight {d : ℕ}
    (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (anisotropicMinusTWeight d) e =
      (localAnisotropicWeight e : ℤ) - e (localT d) := by
  classical
  rw [Finsupp.weight_apply, localAnisotropicWeight,
    Finsupp.sum_fintype _ _ (by simp),
    Finsupp.sum_fintype _ _ (by
      intro i
      rcases i with (_ | (_ | j)) <;> simp)]
  simp_rw [Fintype.sum_option]
  simp [anisotropicMinusTWeight, localT, sub_eq_add_neg, Nat.cast_sum,
    mul_comm]
  ring

private theorem weight_eMinusTWeight {d : ℕ} (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (eMinusTWeight d) e =
      (e (localE d) : ℤ) - e (localT d) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_option, Fintype.sum_option]
  simp [eMinusTWeight, localE, localT, sub_eq_add_neg]
  ring

private theorem weight_negContactWeight {d : ℕ} (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (negContactWeight d) e = -(contactOrder d e : ℤ) := by
  classical
  rw [Finsupp.weight_apply, contactOrder,
    Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
  simp_rw [Fintype.sum_option]
  simp [negContactWeight, contactWeight, Nat.cast_mul, mul_comm]
  ring

private theorem weight_negTWeight {d : ℕ} (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (negTWeight d) e = -(e (localT d) : ℤ) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_option, Fintype.sum_option]
  simp [negTWeight, localT]

private theorem weight_globalFirstWeight {d : ℕ} (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (globalFirstWeight d) u = firstJetExponent u := by
  classical
  rw [Finsupp.weight_apply, firstJetExponent, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_option]
  simp only [globalFirstWeight, nsmul_eq_mul, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : (j : ℕ) = 1 <;> simp [h]

private theorem weight_globalHigherWeight {d : ℕ} (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (globalHigherWeight d) u = fullHigherJetWeight u := by
  classical
  rw [Finsupp.weight_apply, fullHigherJetWeight, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_option]
  simp [globalHigherWeight, Nat.mul_comm]

/-! ## Support of the first coordinate change -/

private def translateGenerator {R : Type*} [CommRing R] {d : ℕ}
    (alpha y : R) : JetVariable d → LocalPolynomial R d
  | none => C alpha + X (localT d)
  | some j => Fin.cases
      (C y + X (localT d) * X (localU d))
      (fun i => X (localY i)) j

private theorem translateVariable_uMinusT_nonpos
    {R : Type*} [CommRing R] {d : ℕ} (alpha y : R)
    (v : JetVariable d) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (translateGenerator alpha y v).support) :
    Finsupp.weight (uMinusTWeight d) e ≤ 0 := by
  cases v with
  | none =>
    exact support_weight_add_le (uMinusTWeight d)
      (fun z hz => (support_weight_C_eq_zero _ _ hz).le)
      (fun z hz => by
        rw [support_weight_X_eq _ (localT d) hz]
        simp [uMinusTWeight, localT]) he
  | some j =>
    cases j using Fin.cases with
    | zero =>
      exact support_weight_add_le (uMinusTWeight d)
        (fun z hz => (support_weight_C_eq_zero _ _ hz).le)
        (fun z hz => by
          have hmul := support_weight_mul_le (uMinusTWeight d)
            (a := (-1 : ℤ)) (b := (1 : ℤ))
            (fun z hz => (support_weight_X_eq _ (localT d) hz).le)
            (fun z hz => (support_weight_X_eq _ (localU d) hz).le) hz
          simpa [uMinusTWeight, localT, localU] using hmul) he
    | succ i =>
      rw [support_weight_X_eq _ (localY i) he]
      simp [uMinusTWeight, localY]

private theorem translateVariable_first_le
    {R : Type*} [CommRing R] {d : ℕ} (alpha y : R)
    (v : JetVariable d) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (translateGenerator alpha y v).support) :
    Finsupp.weight (visibleFirstWeight d) e ≤ globalFirstWeight d v := by
  cases v with
  | none =>
    exact support_weight_add_le (visibleFirstWeight d)
      (fun z hz => by simpa [globalFirstWeight] using
        (support_weight_C_eq_zero (visibleFirstWeight d) _ hz).le)
      (fun z hz => by
        rw [support_weight_X_eq _ (localT d) hz]
        simp [visibleFirstWeight, globalFirstWeight, localT]) he
  | some j =>
    cases j using Fin.cases with
    | zero =>
      exact support_weight_add_le (visibleFirstWeight d)
        (fun z hz => by simpa [globalFirstWeight] using
          (support_weight_C_eq_zero (visibleFirstWeight d) _ hz).le)
        (fun z hz => by
          have hmul := support_weight_mul_le (visibleFirstWeight d)
            (a := 0) (b := 0)
            (fun z hz => (support_weight_X_eq _ (localT d) hz).le)
            (fun z hz => (support_weight_X_eq _ (localU d) hz).le) hz
          simpa [visibleFirstWeight, globalFirstWeight, localT, localU] using hmul) he
    | succ i =>
      rw [support_weight_X_eq _ (localY i) he]
      simp [visibleFirstWeight, globalFirstWeight, localY]

private theorem translateVariable_higher_le
    {R : Type*} [CommRing R] {d : ℕ} (alpha y : R)
    (v : JetVariable d) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (translateGenerator alpha y v).support) :
    Finsupp.weight (visibleAnisotropicWeight d) e ≤ globalHigherWeight d v := by
  cases v with
  | none =>
    exact support_weight_add_le (visibleAnisotropicWeight d)
      (fun z hz => by simpa [globalHigherWeight] using
        (support_weight_C_eq_zero (visibleAnisotropicWeight d) _ hz).le)
      (fun z hz => by
        rw [support_weight_X_eq _ (localT d) hz]
        simp [visibleAnisotropicWeight, globalHigherWeight, localT]) he
  | some j =>
    cases j using Fin.cases with
    | zero =>
      exact support_weight_add_le (visibleAnisotropicWeight d)
        (fun z hz => by simpa [globalHigherWeight] using
          (support_weight_C_eq_zero (visibleAnisotropicWeight d) _ hz).le)
        (fun z hz => by
          have hmul := support_weight_mul_le (visibleAnisotropicWeight d)
            (a := 0) (b := 0)
            (fun z hz => (support_weight_X_eq _ (localT d) hz).le)
            (fun z hz => (support_weight_X_eq _ (localU d) hz).le) hz
          simpa [visibleAnisotropicWeight, globalHigherWeight, localT, localU] using hmul) he
    | succ i =>
      rw [support_weight_X_eq _ (localY i) he]
      simp [visibleAnisotropicWeight, globalHigherWeight, localY]

/-! ## Global support factors through the intermediate local space -/

private theorem mem_support_filterMonomials
    {R : Type*} [CommRing R] {d : ℕ}
    (predicate : (LocalVariable d →₀ ℕ) → Prop) [DecidablePred predicate]
    (F : LocalPolynomial R d) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (filterMonomials (R := R) predicate F).support) :
    predicate e ∧ e ∈ F.support := by
  have hc := he
  rw [MvPolynomial.mem_support_iff, coeff_filterMonomials] at hc
  by_cases h : predicate e
  · simp only [h, if_true] at hc
    exact ⟨h, MvPolynomial.mem_support_iff.mpr hc⟩
  · simp only [h, if_false, ne_eq, not_true_eq_false] at hc

/-- Translating an eligible global polynomial to `T,U,Y` coordinates and
discarding `T`-degree at least `m` lands in the finite intermediate space
`V`. -/
theorem translatedTruncation_mem_localVSpace
    {q d m A K B W C : ℕ} {Q : DifferentialPolynomial q d}
    (hQ : Q ∈ interpolationSpace q d m A K B W C)
    (alpha y : ZMod q) :
    translatedTruncation (d := d) m alpha y Q ∈
      localVSpace (R := ZMod q) (d := d) m W := by
  classical
  rw [localVSpace, localExponentSpan, MvPolynomial.mem_restrictSupport_iff]
  intro e he
  have heFilter := mem_support_filterMonomials
    (R := ZMod q) (d := d) (fun z => z (localT d) < m)
    (translateToU alpha y Q) he
  rcases heFilter with ⟨hT, heTranslate⟩
  change e ∈ (MvPolynomial.bind₁ (translateGenerator alpha y) Q).support at heTranslate
  have hBalance : Finsupp.weight (uMinusTWeight d) e ≤ 0 :=
    support_weight_bind₁_le (fun _ : JetVariable d => (0 : ℤ))
      (uMinusTWeight d) (translateGenerator alpha y)
      (translateVariable_uMinusT_nonpos alpha y)
      (fun u hu => by
        rw [Finsupp.weight_apply]
        simp [Finsupp.sum]) heTranslate
  have hFirst : Finsupp.weight (visibleFirstWeight d) e ≤ m :=
    support_weight_bind₁_le (globalFirstWeight d) (visibleFirstWeight d)
      (translateGenerator alpha y) (translateVariable_first_le alpha y)
      (fun u hu => by
        rw [weight_globalFirstWeight]
        exact (mem_interpolationSpace_iff.mp hQ u hu).1) heTranslate
  have hHigher : Finsupp.weight (visibleAnisotropicWeight d) e ≤ W :=
    support_weight_bind₁_le (globalHigherWeight d)
      (visibleAnisotropicWeight d) (translateGenerator alpha y)
      (translateVariable_higher_le alpha y)
      (fun u hu => by
        rw [weight_globalHigherWeight]
        exact (mem_interpolationSpace_iff.mp hQ u hu).2.2.2.1) heTranslate
  refine ⟨hT, ?_, ?_, ?_⟩
  · rw [weight_uMinusTWeight] at hBalance
    exact_mod_cast (sub_nonpos.mp hBalance)
  · rw [weight_visibleFirstWeight] at hFirst
    exact hFirst
  · rw [weight_visibleAnisotropicWeight] at hHigher
    exact hHigher.trans (Nat.le_add_right W (e (localT d)))

/-! ## Low contact terms are insensitive to the preliminary truncation -/

private def rewriteGenerator {R : Type*} [CommRing R] {d : ℕ} :
    LocalVariable d → LocalPolynomial R d
  | none => X (localT d)
  | some none => X (localE d) + localJetSum (R := R) (d := d)
  | some (some j) => X (localY j)

private theorem localJetTerm_negContact_nonpos
    {R : Type*} [CommRing R] {d : ℕ} (j : Fin d)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (localJetTerm (R := R) j).support) :
    Finsupp.weight (negContactWeight d) e ≤ 0 := by
  change e ∈
    (C ((-1 : R) ^ ((j : ℕ) + 2)) *
      X (localT d) ^ (j : ℕ) * X (localY j)).support at he
  have hpow : ∀ z ∈ (X (localT d) ^ (j : ℕ) : LocalPolynomial R d).support,
      Finsupp.weight (negContactWeight d) z ≤ 0 := by
    intro z hz
    have h := support_weight_pow_le (negContactWeight d)
      (a := (-1 : ℤ))
      (fun z hz => (support_weight_X_eq _ (localT d) hz).le)
      (j : ℕ) hz
    simpa [negContactWeight, localT] using h.trans (by simp :
      (j : ℕ) • (-1 : ℤ) ≤ 0)
  have hleft : ∀ z ∈
      (C ((-1 : R) ^ ((j : ℕ) + 2)) * X (localT d) ^ (j : ℕ)).support,
      Finsupp.weight (negContactWeight d) z ≤ 0 := by
    intro z hz
    simpa using support_weight_mul_le (negContactWeight d)
      (a := (0 : ℤ)) (b := (0 : ℤ))
      (fun z hz => (support_weight_C_eq_zero _ _ hz).le) hpow hz
  simpa [negContactWeight, localY] using support_weight_mul_le
    (negContactWeight d) (a := (0 : ℤ)) (b := (0 : ℤ)) hleft
    (fun z hz => (support_weight_X_eq _ (localY j) hz).le) he

private theorem rewriteVariable_negContact_le_negT
    {R : Type*} [CommRing R] {d : ℕ} (v : LocalVariable d)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (rewriteGenerator (R := R) v).support) :
    Finsupp.weight (negContactWeight d) e ≤ negTWeight d v := by
  rcases v with (_ | (_ | j))
  · rw [support_weight_X_eq _ (localT d) he]
    simp [negContactWeight, negTWeight, localT]
  · exact support_weight_add_le (negContactWeight d)
      (fun z hz => by
        rw [support_weight_X_eq _ (localE d) hz]
        simp [negContactWeight, negTWeight, localE])
      (fun z hz => by
        exact support_weight_sum_le (negContactWeight d) Finset.univ
          (fun j : Fin d => localJetTerm (R := R) j)
          (fun j hj z hz => localJetTerm_negContact_nonpos j hz) hz) he
  · rw [support_weight_X_eq _ (localY j) he]
    simp [negContactWeight, negTWeight, localY]

private theorem truncateLocalT_add_highPart
    {R : Type*} [CommRing R] {d m : ℕ} (F : LocalPolynomial R d) :
    truncateLocalT (R := R) (d := d) m F +
      filterMonomials (R := R) (fun e => ¬e (localT d) < m) F = F := by
  classical
  apply MvPolynomial.ext
  intro e
  rw [MvPolynomial.coeff_add, truncateLocalT, coeff_filterMonomials,
    coeff_filterMonomials]
  by_cases h : e (localT d) < m <;> simp [h]

private theorem projectLowContact_rewrite_highPart_eq_zero
    {R : Type*} [CommRing R] {d m : ℕ} (F : LocalPolynomial R d) :
    projectLowContact (R := R) (d := d) m
        (rewriteUToE (filterMonomials (R := R)
          (fun e => ¬e (localT d) < m) F)) = 0 := by
  classical
  let H : LocalPolynomial R d :=
    filterMonomials (R := R) (fun e => ¬e (localT d) < m) F
  change projectLowContact (R := R) (d := d) m (rewriteUToE H) = 0
  have hSource : ∀ u ∈ H.support,
      Finsupp.weight (negTWeight d) u ≤ -(m : ℤ) := by
    intro u hu
    have hu' := mem_support_filterMonomials
      (R := R) (d := d) (fun e => ¬e (localT d) < m) F hu
    rw [weight_negTWeight]
    omega
  have hRewrite : ∀ e ∈ (rewriteUToE H).support,
      Finsupp.weight (negContactWeight d) e ≤ -(m : ℤ) := by
    intro e he
    change e ∈ (MvPolynomial.bind₁ (rewriteGenerator (R := R)) H).support at he
    exact support_weight_bind₁_le (negTWeight d) (negContactWeight d)
      (rewriteGenerator (R := R)) rewriteVariable_negContact_le_negT hSource he
  apply MvPolynomial.ext
  intro e
  rw [MvPolynomial.coeff_zero, projectLowContact, coeff_filterMonomials]
  by_cases hcontact : contactOrder d e < m
  · simp only [hcontact, if_true]
    by_contra hcoeff
    have he : e ∈ (rewriteUToE H).support :=
      MvPolynomial.mem_support_iff.mpr hcoeff
    have hbound := hRewrite e he
    rw [weight_negContactWeight] at hbound
    omega
  · simp [hcontact]

private theorem projectLowContact_rewrite_eq_truncated
    {R : Type*} [CommRing R] {d m : ℕ} (F : LocalPolynomial R d) :
    projectLowContact (R := R) (d := d) m (rewriteUToE F) =
      projectLowContact (R := R) (d := d) m
        (rewriteUToE (truncateLocalT (R := R) (d := d) m F)) := by
  let H : LocalPolynomial R d :=
    filterMonomials (R := R) (fun e => ¬e (localT d) < m) F
  have hdecomp : truncateLocalT (R := R) (d := d) m F + H = F :=
    truncateLocalT_add_highPart F
  have hzero : projectLowContact (R := R) (d := d) m (rewriteUToE H) = 0 :=
    projectLowContact_rewrite_highPart_eq_zero F
  calc
    projectLowContact (R := R) (d := d) m (rewriteUToE F) =
        projectLowContact (R := R) (d := d) m
          (rewriteUToE (truncateLocalT (R := R) (d := d) m F + H)) :=
      congrArg (fun G => projectLowContact (R := R) (d := d) m (rewriteUToE G))
        hdecomp.symm
    _ = projectLowContact (R := R) (d := d) m
          (rewriteUToE (truncateLocalT (R := R) (d := d) m F)) +
        projectLowContact (R := R) (d := d) m (rewriteUToE H) := by
      rw [map_add, map_add]
    _ = projectLowContact (R := R) (d := d) m
          (rewriteUToE (truncateLocalT (R := R) (d := d) m F)) := by
      rw [hzero, add_zero]

/-- Rewriting `U` to `E` cannot turn a term discarded modulo `T^m` into a
low-contact term.  Consequently the received-word constraint map factors
through `translatedTruncation`. -/
theorem receivedConstraintMap_eq_localConstraintMap_translatedTruncation
    {R : Type*} [CommRing R] {d m : ℕ} (alpha y : R)
    (Q : MvPolynomial (JetVariable d) R) :
    receivedConstraintMap (d := d) m alpha y Q =
      localConstraintMap (d := d) m (translatedTruncation m alpha y Q) := by
  exact projectLowContact_rewrite_eq_truncated (translateToU alpha y Q)

/-! ## The universal local map lands in the contact envelope -/

private theorem localJetTerm_first_le_one
    {R : Type*} [CommRing R] {d : ℕ} (j : Fin d)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (localJetTerm (R := R) j).support) :
    Finsupp.weight (visibleFirstWeight d) e ≤ 1 := by
  change e ∈
    (C ((-1 : R) ^ ((j : ℕ) + 2)) *
      X (localT d) ^ (j : ℕ) * X (localY j)).support at he
  have hpow : ∀ z ∈ (X (localT d) ^ (j : ℕ) : LocalPolynomial R d).support,
      Finsupp.weight (visibleFirstWeight d) z ≤ 0 := by
    intro z hz
    simpa [visibleFirstWeight, localT] using
      (support_weight_pow_le (visibleFirstWeight d) (a := 0)
        (fun z hz => (support_weight_X_eq _ (localT d) hz).le) (j : ℕ) hz)
  have hleft : ∀ z ∈
      (C ((-1 : R) ^ ((j : ℕ) + 2)) * X (localT d) ^ (j : ℕ)).support,
      Finsupp.weight (visibleFirstWeight d) z ≤ 0 := by
    intro z hz
    simpa using support_weight_mul_le (visibleFirstWeight d)
      (a := 0) (b := 0)
      (fun z hz => (support_weight_C_eq_zero _ _ hz).le) hpow hz
  have hY : ∀ z ∈ (X (localY j) : LocalPolynomial R d).support,
      Finsupp.weight (visibleFirstWeight d) z ≤ 1 := by
    intro z hz
    rw [support_weight_X_eq _ (localY j) hz]
    by_cases h : (j : ℕ) = 0 <;> simp [visibleFirstWeight, localY, h]
  simpa using support_weight_mul_le (visibleFirstWeight d)
    (a := 0) (b := 1) hleft hY he

private theorem localJetTerm_firstMinusT_le_one
    {R : Type*} [CommRing R] {d : ℕ} (j : Fin d)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (localJetTerm (R := R) j).support) :
    Finsupp.weight (firstMinusTWeight d) e ≤ 1 := by
  change e ∈
    (C ((-1 : R) ^ ((j : ℕ) + 2)) *
      X (localT d) ^ (j : ℕ) * X (localY j)).support at he
  have hpow : ∀ z ∈ (X (localT d) ^ (j : ℕ) : LocalPolynomial R d).support,
      Finsupp.weight (firstMinusTWeight d) z ≤ -(j : ℤ) := by
    intro z hz
    simpa [firstMinusTWeight, localT] using
      (support_weight_pow_le (firstMinusTWeight d) (a := (-1 : ℤ))
        (fun z hz => (support_weight_X_eq _ (localT d) hz).le)
        (j : ℕ) hz)
  have hleft : ∀ z ∈
      (C ((-1 : R) ^ ((j : ℕ) + 2)) * X (localT d) ^ (j : ℕ)).support,
      Finsupp.weight (firstMinusTWeight d) z ≤ -(j : ℤ) := by
    intro z hz
    simpa using support_weight_mul_le (firstMinusTWeight d)
      (a := (0 : ℤ)) (b := -(j : ℤ))
      (fun z hz => (support_weight_C_eq_zero _ _ hz).le) hpow hz
  have hY : ∀ z ∈ (X (localY j) : LocalPolynomial R d).support,
      Finsupp.weight (firstMinusTWeight d) z ≤ 1 := by
    intro z hz
    rw [support_weight_X_eq _ (localY j) hz]
    by_cases h : (j : ℕ) = 0 <;>
      simp [firstMinusTWeight, localY, h]
  have h := support_weight_mul_le (firstMinusTWeight d)
    (a := -(j : ℤ)) (b := (1 : ℤ)) hleft hY he
  omega

private theorem localJetTerm_anisotropicMinusContact_nonpos
    {R : Type*} [CommRing R] {d : ℕ} (j : Fin d)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (localJetTerm (R := R) j).support) :
    Finsupp.weight (anisotropicMinusContactWeight d) e ≤ 0 := by
  change e ∈
    (C ((-1 : R) ^ ((j : ℕ) + 2)) *
      X (localT d) ^ (j : ℕ) * X (localY j)).support at he
  have hpow : ∀ z ∈ (X (localT d) ^ (j : ℕ) : LocalPolynomial R d).support,
      Finsupp.weight (anisotropicMinusContactWeight d) z ≤ -(j : ℤ) := by
    intro z hz
    simpa [anisotropicMinusContactWeight, localT] using
      (support_weight_pow_le (anisotropicMinusContactWeight d) (a := (-1 : ℤ))
        (fun z hz => (support_weight_X_eq _ (localT d) hz).le) (j : ℕ) hz)
  have hleft : ∀ z ∈
      (C ((-1 : R) ^ ((j : ℕ) + 2)) * X (localT d) ^ (j : ℕ)).support,
      Finsupp.weight (anisotropicMinusContactWeight d) z ≤ -(j : ℤ) := by
    intro z hz
    have h := support_weight_mul_le (anisotropicMinusContactWeight d)
      (a := (0 : ℤ)) (b := -(j : ℤ))
      (fun z hz => (support_weight_C_eq_zero _ _ hz).le) hpow hz
    simpa using h
  have hY : ∀ z ∈ (X (localY j) : LocalPolynomial R d).support,
      Finsupp.weight (anisotropicMinusContactWeight d) z ≤ (j : ℤ) := by
    intro z hz
    rw [support_weight_X_eq _ (localY j) hz]
    simp [anisotropicMinusContactWeight, localY]
  have h := support_weight_mul_le (anisotropicMinusContactWeight d)
    (a := -(j : ℤ)) (b := (j : ℤ)) hleft hY he
  simpa using h

private theorem rewriteVariable_first_le_firstPlusU
    {R : Type*} [CommRing R] {d : ℕ} (v : LocalVariable d)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (rewriteGenerator (R := R) v).support) :
    Finsupp.weight (visibleFirstWeight d) e ≤ firstPlusUWeight d v := by
  rcases v with (_ | (_ | j))
  · rw [support_weight_X_eq _ (localT d) he]
    simp [visibleFirstWeight, firstPlusUWeight, localT]
  · exact support_weight_add_le (visibleFirstWeight d)
      (fun z hz => by
        rw [support_weight_X_eq _ (localE d) hz]
        simp [visibleFirstWeight, localE])
      (fun z hz => support_weight_sum_le (visibleFirstWeight d) Finset.univ
        (fun j : Fin d => localJetTerm (R := R) j)
        (fun j hj z hz => localJetTerm_first_le_one j hz) hz) he
  · rw [support_weight_X_eq _ (localY j) he]
    simp [visibleFirstWeight, firstPlusUWeight, localY]

private theorem rewriteVariable_firstMinusT_le_firstPlusUMinusT
    {R : Type*} [CommRing R] {d : ℕ} (v : LocalVariable d)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (rewriteGenerator (R := R) v).support) :
    Finsupp.weight (firstMinusTWeight d) e ≤
      firstPlusUMinusTWeight d v := by
  rcases v with (_ | (_ | j))
  · rw [support_weight_X_eq _ (localT d) he]
    simp [firstMinusTWeight, firstPlusUMinusTWeight, localT]
  · exact support_weight_add_le (firstMinusTWeight d)
      (fun z hz => by
        rw [support_weight_X_eq _ (localE d) hz]
        simp [firstMinusTWeight, localE])
      (fun z hz => support_weight_sum_le (firstMinusTWeight d) Finset.univ
        (fun j : Fin d => localJetTerm (R := R) j)
        (fun j hj z hz => localJetTerm_firstMinusT_le_one j hz) hz) he
  · rw [support_weight_X_eq _ (localY j) he]
    simp [firstMinusTWeight, firstPlusUMinusTWeight, localY]

private theorem rewriteVariable_anisotropicMinusContact_le
    {R : Type*} [CommRing R] {d : ℕ} (v : LocalVariable d)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (rewriteGenerator (R := R) v).support) :
    Finsupp.weight (anisotropicMinusContactWeight d) e ≤
      anisotropicMinusTWeight d v := by
  rcases v with (_ | (_ | j))
  · rw [support_weight_X_eq _ (localT d) he]
    simp [anisotropicMinusContactWeight, anisotropicMinusTWeight, localT]
  · exact support_weight_add_le (anisotropicMinusContactWeight d)
      (fun z hz => by
        rw [support_weight_X_eq _ (localE d) hz]
        simp [anisotropicMinusContactWeight, localE])
      (fun z hz => support_weight_sum_le (anisotropicMinusContactWeight d)
        Finset.univ (fun j : Fin d => localJetTerm (R := R) j)
        (fun j hj z hz => localJetTerm_anisotropicMinusContact_nonpos j hz) hz) he
  · rw [support_weight_X_eq _ (localY j) he]
    simp [anisotropicMinusContactWeight, anisotropicMinusTWeight, localY]

private theorem rewriteVariable_eMinusT_le_uMinusT
    {R : Type*} [CommRing R] {d : ℕ} (v : LocalVariable d)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (rewriteGenerator (R := R) v).support) :
    Finsupp.weight (eMinusTWeight d) e ≤ uMinusTWeight d v := by
  rcases v with (_ | (_ | j))
  · rw [support_weight_X_eq _ (localT d) he]
    simp [eMinusTWeight, uMinusTWeight, localT]
  · exact support_weight_add_le (eMinusTWeight d) (a := (1 : ℤ))
      (fun z hz => by
        rw [support_weight_X_eq _ (localE d) hz]
        simp [eMinusTWeight, localE])
      (fun z hz => support_weight_sum_le (eMinusTWeight d) Finset.univ
        (fun j : Fin d => localJetTerm (R := R) j)
        (fun j _hj z hz => by
          change z ∈
            (C ((-1 : R) ^ ((j : ℕ) + 2)) *
              X (localT d) ^ (j : ℕ) * X (localY j)).support at hz
          have hpow : ∀ u ∈
              (X (localT d) ^ (j : ℕ) : LocalPolynomial R d).support,
              Finsupp.weight (eMinusTWeight d) u ≤ 0 := by
            intro u hu
            exact (support_weight_pow_le (eMinusTWeight d) (a := (-1 : ℤ))
              (fun u hu => (support_weight_X_eq _ (localT d) hu).le)
              (j : ℕ) hu).trans (by simp)
          have hleft : ∀ u ∈
              (C ((-1 : R) ^ ((j : ℕ) + 2)) *
                X (localT d) ^ (j : ℕ)).support,
              Finsupp.weight (eMinusTWeight d) u ≤ 0 := by
            intro u hu
            simpa using support_weight_mul_le (eMinusTWeight d)
              (a := (0 : ℤ)) (b := (0 : ℤ))
              (fun u hu => (support_weight_C_eq_zero _ _ hu).le) hpow hu
          have hzero : Finsupp.weight (eMinusTWeight d) z ≤ 0 := by
            simpa [eMinusTWeight, localY] using support_weight_mul_le
              (eMinusTWeight d) (a := (0 : ℤ)) (b := (0 : ℤ)) hleft
              (fun u hu => (support_weight_X_eq _ (localY j) hu).le) hz
          exact hzero.trans (by omega)) hz) he
  · rw [support_weight_X_eq _ (localY j) he]
    simp [eMinusTWeight, uMinusTWeight, localY]

private theorem rewriteVariable_anisotropicMinusT_le
    {R : Type*} [CommRing R] {d : ℕ} (v : LocalVariable d)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (rewriteGenerator (R := R) v).support) :
    Finsupp.weight (anisotropicMinusTWeight d) e ≤
      anisotropicMinusTWeight d v := by
  rcases v with (_ | (_ | j))
  · rw [support_weight_X_eq _ (localT d) he]
    simp [anisotropicMinusTWeight, localT]
  · exact support_weight_add_le (anisotropicMinusTWeight d)
      (fun z hz => by
        rw [support_weight_X_eq _ (localE d) hz]
        simp [anisotropicMinusTWeight, localE])
      (fun z hz => support_weight_sum_le (anisotropicMinusTWeight d)
        Finset.univ (fun j : Fin d => localJetTerm (R := R) j)
        (fun j _hj z hz => by
          change z ∈
            (C ((-1 : R) ^ ((j : ℕ) + 2)) *
              X (localT d) ^ (j : ℕ) * X (localY j)).support at hz
          have hpow : ∀ u ∈
              (X (localT d) ^ (j : ℕ) : LocalPolynomial R d).support,
              Finsupp.weight (anisotropicMinusTWeight d) u ≤ -(j : ℤ) := by
            intro u hu
            simpa [anisotropicMinusTWeight, localT] using
              (support_weight_pow_le (anisotropicMinusTWeight d)
                (a := (-1 : ℤ))
                (fun u hu => (support_weight_X_eq _ (localT d) hu).le)
                (j : ℕ) hu)
          have hleft : ∀ u ∈
              (C ((-1 : R) ^ ((j : ℕ) + 2)) *
                X (localT d) ^ (j : ℕ)).support,
              Finsupp.weight (anisotropicMinusTWeight d) u ≤ -(j : ℤ) := by
            intro u hu
            simpa using support_weight_mul_le (anisotropicMinusTWeight d)
              (a := (0 : ℤ)) (b := -(j : ℤ))
              (fun u hu => (support_weight_C_eq_zero _ _ hu).le) hpow hu
          simpa [anisotropicMinusTWeight, localY] using support_weight_mul_le
            (anisotropicMinusTWeight d) (a := -(j : ℤ)) (b := (j : ℤ))
            hleft (fun u hu => by
              rw [support_weight_X_eq _ (localY j) hu]
              simp [anisotropicMinusTWeight, localY]) hz) hz) he
  · rw [support_weight_X_eq _ (localY j) he]
    simp [anisotropicMinusTWeight, localY]

/-- The low-contact projection of the `U`-to-`E` rewrite of a polynomial in
`V` has exactly the support bounds defining the contact-envelope space. -/
theorem localConstraintMap_mem_contactEnvelopeSpace
    {R : Type*} [CommRing R] {d m W : ℕ} {F : LocalPolynomial R d}
    (hF : F ∈ localVSpace (R := R) (d := d) m W) :
    localConstraintMap (R := R) (d := d) m F ∈
      contactEnvelopeSpace (R := R) (d := d) m W := by
  classical
  rw [contactEnvelopeSpace, localExponentSpan,
    MvPolynomial.mem_restrictSupport_iff]
  intro e he
  change e ∈ (projectLowContact (R := R) (d := d) m (rewriteUToE F)).support at he
  have heFilter := mem_support_filterMonomials
    (R := R) (d := d) (fun z => contactOrder d z < m) (rewriteUToE F) he
  rcases heFilter with ⟨hContact, heRewrite⟩
  rw [localVSpace, localExponentSpan,
    MvPolynomial.mem_restrictSupport_iff] at hF
  have hFirst : Finsupp.weight (visibleFirstWeight d) e ≤ 2 * m - 1 :=
    support_weight_bind₁_le (firstPlusUWeight d) (visibleFirstWeight d)
      (rewriteGenerator (R := R)) rewriteVariable_first_le_firstPlusU
      (fun u hu => by
        rw [weight_firstPlusUWeight]
        have hVu : VExponent (d := d) m W u := hF hu
        rcases hVu with ⟨hT, hU, hY, hWeight⟩
        omega) (by
          change e ∈ (MvPolynomial.bind₁ (rewriteGenerator (R := R)) F).support
          exact heRewrite)
  have hSigned : Finsupp.weight (anisotropicMinusContactWeight d) e ≤ (W : ℤ) :=
    support_weight_bind₁_le (anisotropicMinusTWeight d)
      (anisotropicMinusContactWeight d) (rewriteGenerator (R := R))
      rewriteVariable_anisotropicMinusContact_le
      (fun u hu => by
        rw [weight_anisotropicMinusTWeight]
        have hVu : VExponent (d := d) m W u := hF hu
        rcases hVu with ⟨hT, hU, hY, hWeight⟩
        omega) (by
          change e ∈ (MvPolynomial.bind₁ (rewriteGenerator (R := R)) F).support
          exact heRewrite)
  refine ⟨hContact, ?_, ?_⟩
  · rw [weight_visibleFirstWeight] at hFirst
    exact hFirst
  · rw [weight_anisotropicMinusContactWeight] at hSigned
    omega

/-- The local constraint map actually lands in the strictly smaller coupled
envelope.  The allowances are indexed by the output monomial's own `T`
exponent and contact order. -/
theorem localConstraintMap_mem_coupledContactEnvelopeSpace
    {R : Type*} [CommRing R] {d m W : ℕ} {F : LocalPolynomial R d}
    (hF : F ∈ localVSpace (R := R) (d := d) m W) :
    localConstraintMap (R := R) (d := d) m F ∈
      coupledContactEnvelopeSpace (R := R) (d := d) m W := by
  classical
  rw [coupledContactEnvelopeSpace, localExponentSpan,
    MvPolynomial.mem_restrictSupport_iff]
  intro e he
  change e ∈ (projectLowContact (R := R) (d := d) m
    (rewriteUToE F)).support at he
  have heFilter := mem_support_filterMonomials
    (R := R) (d := d) (fun z => contactOrder d z < m) (rewriteUToE F) he
  rcases heFilter with ⟨hContact, heRewrite⟩
  rw [localVSpace, localExponentSpan,
    MvPolynomial.mem_restrictSupport_iff] at hF
  have hFirstSigned :
      Finsupp.weight (firstMinusTWeight d) e ≤ (m : ℤ) :=
    support_weight_bind₁_le (firstPlusUMinusTWeight d)
      (firstMinusTWeight d) (rewriteGenerator (R := R))
      rewriteVariable_firstMinusT_le_firstPlusUMinusT
      (fun u hu => by
        rw [weight_firstPlusUMinusTWeight]
        have hVu : VExponent (d := d) m W u := hF hu
        rcases hVu with ⟨hT, hU, hY, hWeight⟩
        omega) (by
          change e ∈ (MvPolynomial.bind₁ (rewriteGenerator (R := R)) F).support
          exact heRewrite)
  have hSigned : Finsupp.weight (anisotropicMinusContactWeight d) e ≤ (W : ℤ) :=
    support_weight_bind₁_le (anisotropicMinusTWeight d)
      (anisotropicMinusContactWeight d) (rewriteGenerator (R := R))
      rewriteVariable_anisotropicMinusContact_le
      (fun u hu => by
        rw [weight_anisotropicMinusTWeight]
        have hVu : VExponent (d := d) m W u := hF hu
        rcases hVu with ⟨hT, hU, hY, hWeight⟩
        omega) (by
          change e ∈ (MvPolynomial.bind₁ (rewriteGenerator (R := R)) F).support
          exact heRewrite)
  refine ⟨hContact, ?_, ?_⟩
  · rw [weight_firstMinusTWeight] at hFirstSigned
    omega
  · rw [weight_anisotropicMinusContactWeight] at hSigned
    omega

/-- The local constraint map retains both signed rewrite invariants, giving
the strongest support-only codomain used by the finite evaluator. -/
theorem localConstraintMap_mem_sharpenedContactEnvelopeSpace
    {R : Type*} [CommRing R] {d m W : ℕ} {F : LocalPolynomial R d}
    (hF : F ∈ localVSpace (R := R) (d := d) m W) :
    localConstraintMap (R := R) (d := d) m F ∈
      sharpenedContactEnvelopeSpace (R := R) (d := d) m W := by
  classical
  rw [sharpenedContactEnvelopeSpace, localExponentSpan,
    MvPolynomial.mem_restrictSupport_iff]
  intro e he
  change e ∈ (projectLowContact (R := R) (d := d) m
    (rewriteUToE F)).support at he
  have heFilter := mem_support_filterMonomials
    (R := R) (d := d) (fun z => contactOrder d z < m) (rewriteUToE F) he
  rcases heFilter with ⟨hContact, heRewrite⟩
  rw [localVSpace, localExponentSpan,
    MvPolynomial.mem_restrictSupport_iff] at hF
  have hE : Finsupp.weight (eMinusTWeight d) e ≤ 0 :=
    support_weight_bind₁_le (uMinusTWeight d) (eMinusTWeight d)
      (rewriteGenerator (R := R)) rewriteVariable_eMinusT_le_uMinusT
      (fun u hu => by
        rw [weight_uMinusTWeight]
        exact sub_nonpos.mpr (by exact_mod_cast (hF hu).2.1))
      (by
        change e ∈ (MvPolynomial.bind₁ (rewriteGenerator (R := R)) F).support
        exact heRewrite)
  have hFirstSigned :
      Finsupp.weight (firstMinusTWeight d) e ≤ (m : ℤ) :=
    support_weight_bind₁_le (firstPlusUMinusTWeight d)
      (firstMinusTWeight d) (rewriteGenerator (R := R))
      rewriteVariable_firstMinusT_le_firstPlusUMinusT
      (fun u hu => by
        rw [weight_firstPlusUMinusTWeight]
        rcases hF hu with ⟨_hT, hU, hY, _hWeight⟩
        omega)
      (by
        change e ∈ (MvPolynomial.bind₁ (rewriteGenerator (R := R)) F).support
        exact heRewrite)
  have hHigher :
      Finsupp.weight (anisotropicMinusTWeight d) e ≤ (W : ℤ) :=
    support_weight_bind₁_le (anisotropicMinusTWeight d)
      (anisotropicMinusTWeight d) (rewriteGenerator (R := R))
      rewriteVariable_anisotropicMinusT_le
      (fun u hu => by
        rw [weight_anisotropicMinusTWeight]
        exact sub_le_iff_le_add.mpr (by exact_mod_cast (hF hu).2.2.2))
      (by
        change e ∈ (MvPolynomial.bind₁ (rewriteGenerator (R := R)) F).support
        exact heRewrite)
  refine ⟨hContact, ?_, ?_, ?_⟩
  · rw [weight_eMinusTWeight] at hE
    exact_mod_cast sub_nonpos.mp hE
  · rw [weight_firstMinusTWeight] at hFirstSigned
    omega
  · rw [weight_anisotropicMinusTWeight] at hHigher
    omega

end RSListDecoding
