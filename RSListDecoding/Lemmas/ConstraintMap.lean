import RSListDecoding.Defs.ConstraintMap

/-!
# Elementary properties of the local constraint maps

These lemmas identify the coefficient-vector formulation of the manuscript's
local conditions with the low-contact polynomial projection used in the rank
argument.
-/

noncomputable section

namespace RSListDecoding

variable {R : Type*} [CommRing R]
variable {d : ℕ}

theorem filterMonomials_eq_zero_iff
    (predicate : (LocalVariable d →₀ ℕ) → Prop)
    [DecidablePred predicate] (F : LocalPolynomial R d) :
    filterMonomials (R := R) predicate F = 0 ↔
      ∀ e, predicate e → MvPolynomial.coeff e F = 0 := by
  rw [← AddMonoidAlgebra.coeff_eq_zero]
  change Finsupp.filter predicate (AddMonoidAlgebra.coeff F) = 0 ↔ _
  simpa only [MvPolynomial.coeff] using
    (Finsupp.filter_eq_zero_iff (p := predicate)
      (f := AddMonoidAlgebra.coeff F))

theorem projectLowContact_eq_zero_iff (m : ℕ) (F : LocalPolynomial R d) :
    projectLowContact (R := R) (d := d) m F = 0 ↔
      ∀ e, contactOrder d e < m → MvPolynomial.coeff e F = 0 := by
  exact filterMonomials_eq_zero_iff
    (R := R) (d := d) (fun e ↦ contactOrder d e < m) F

theorem lowContactCoefficients_eq_zero_iff (m : ℕ)
    (F : LocalPolynomial R d) :
    lowContactCoefficients (R := R) (d := d) m F = 0 ↔
      ∀ e, contactOrder d e < m → MvPolynomial.coeff e F = 0 := by
  constructor
  · intro h e he
    have happ := congrFun h ⟨e, he⟩
    have hz : (0 : LowContactIndex d m → R) ⟨e, he⟩ = 0 := rfl
    rw [hz] at happ
    simpa [lowContactCoefficients] using happ
  · intro h
    ext e
    simpa [lowContactCoefficients] using h e.1 e.2

/-- The paper's coefficient-family condition is exactly vanishing of the
low-contact projection. -/
theorem satisfiesLocalConstraints_iff_receivedConstraintMap_eq_zero
    (m : ℕ) (alpha y : R) (Q : MvPolynomial (JetVariable d) R) :
    SatisfiesLocalConstraints m alpha y Q ↔
      receivedConstraintMap (R := R) (d := d) m alpha y Q = 0 := by
  rw [SatisfiesLocalConstraints, lowContactCoefficients_eq_zero_iff,
    receivedConstraintMap, LinearMap.comp_apply,
    projectLowContact_eq_zero_iff]
  rfl

end RSListDecoding
