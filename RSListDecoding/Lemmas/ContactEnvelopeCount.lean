import RSListDecoding.Lemmas.ScaledLattice
import RSListDecoding.Defs.LocalConstraints
import Mathlib.Data.Finsupp.Order
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Counting the low-contact envelope

Instead of the manuscript's more elaborate kernel subtraction, the local
constraint rank can be bounded directly by its finite contact-envelope
codomain.  This loses only an absolute constant and leaves the decisive
factor `1/d`; the existential `ε₀(θ)` absorbs that constant.
-/

noncomputable section

open scoped BigOperators

namespace RSListDecoding

/-- The `i`-th higher local coordinate is `Y_{i+2}`. -/
def localHigherIndex {d : ℕ} (i : Fin (d - 1)) : Fin d :=
  ⟨i.val + 1, by omega⟩

/-- Restrict a local exponent to `Y₂,...,Y_d`. -/
def localHigherExponent {d : ℕ}
    (e : LocalVariable d →₀ ℕ) : ScaledExponent d :=
  fun i ↦ e (localY (localHigherIndex i))

@[simp]
theorem scaledWeight_localHigherExponent {d : ℕ}
    (e : LocalVariable d →₀ ℕ) :
    scaledWeight (localHigherExponent e) = localAnisotropicWeight e := by
  classical
  cases d with
  | zero =>
      simp [scaledWeight, localHigherExponent, localAnisotropicWeight,
        Finsupp.sum_fintype]
  | succ n =>
      rw [localAnisotropicWeight,
        Finsupp.sum_fintype _ _ (by
          intro v
          rcases v with (_ | (_ | j)) <;> simp),
        Fintype.sum_option, Fintype.sum_option]
      simp only [localHigherExponent, scaledWeight, localY, Nat.succ_sub_one]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, zero_mul, zero_add]
      apply Finset.sum_congr rfl
      intro i _hi
      congr 2

/-- In positive derivative depth, the local first-jet weight is the actual
`Y₁` exponent. -/
theorem localFirstJetExponent_eq {d : ℕ} (hd : 0 < d)
    (e : LocalVariable d →₀ ℕ) :
    localFirstJetExponent e = e (localY ⟨0, hd⟩) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  rw [localFirstJetExponent,
    Finsupp.sum_fintype _ _ (by
      intro v
      rcases v with (_ | (_ | j)) <;> simp),
    Fintype.sum_option, Fintype.sum_option, Fin.sum_univ_succ]
  simp [localY]

/-- Each weighted coordinate contribution is bounded by the total contact
order. -/
theorem contactWeight_mul_exponent_le_contactOrder {d : ℕ}
    (e : LocalVariable d →₀ ℕ) (v : LocalVariable d) :
    contactWeight d v * e v ≤ contactOrder d e := by
  rw [contactOrder, Finsupp.sum]
  by_cases hv : e v = 0
  · simp [hv]
  · exact Finset.single_le_sum
      (f := fun a : LocalVariable d ↦ contactWeight d a * e a)
      (fun _ _ ↦ Nat.zero_le _) (Finsupp.mem_support_iff.mpr hv)

/-- A low-contact exponent has bounded `E` exponent. -/
theorem localE_exponent_le_div {d m : ℕ} (hd : 0 < d)
    (e : LocalVariable d →₀ ℕ)
    (he : contactOrder d e < m) :
    e (localE d) ≤ m / d := by
  rw [Nat.le_div_iff_mul_le hd]
  rw [Nat.mul_comm]
  simpa [contactWeight, localE] using
    ((contactWeight_mul_exponent_le_contactOrder e (localE d)).trans he.le)

/-- The finite product into which every contact-envelope exponent injects. -/
abbrev ContactEnvelopeCode (d m W : ℕ) :=
  Fin m × Fin (m / d + 1) × Fin (2 * m) × BoundedScaledExponent d (W + m)

/-- Encode the four independent pieces of a contact-envelope monomial. -/
def encodeContactEnvelope {d m W : ℕ} (hd : 0 < d)
    (e : {e : LocalVariable d →₀ ℕ // ContactEnvelopeExponent (d := d) m W e}) :
    ContactEnvelopeCode d m W :=
  (⟨e.1 (localT d), by
      simpa [contactWeight, localT] using
        ((contactWeight_mul_exponent_le_contactOrder e.1 (localT d)).trans_lt e.2.1)⟩,
   ⟨e.1 (localE d), Nat.lt_succ_of_le (localE_exponent_le_div hd e.1 e.2.1)⟩,
   ⟨localFirstJetExponent e.1, by
      have hm : 0 < m := Nat.zero_lt_of_lt e.2.1
      have := e.2.2.1
      omega⟩,
   ⟨localHigherExponent e.1, by
      rw [mem_scaledExponentFinset, scaledWeight_localHigherExponent]
      exact e.2.2.2.trans (by omega)⟩)

theorem encodeContactEnvelope_injective {d m W : ℕ} (hd : 0 < d) :
    Function.Injective (encodeContactEnvelope (m := m) (W := W) hd) := by
  intro e f hef
  apply Subtype.ext
  apply Finsupp.ext
  intro v
  rcases v with (_ | (_ | j))
  · exact congrArg (fun z : ContactEnvelopeCode d m W => z.1.val) hef
  · exact congrArg (fun z : ContactEnvelopeCode d m W => z.2.1.val) hef
  · have hfirst := congrArg
        (fun z : ContactEnvelopeCode d m W => z.2.2.1.val) hef
    have hhigher := congrArg
        (fun z : ContactEnvelopeCode d m W => z.2.2.2.1) hef
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [encodeContactEnvelope, localFirstJetExponent_eq,
        localY] using hfirst
    · exact congrFun hhigher i

/-- The direct finite codomain count for the contact constraints. -/
theorem natCard_contactEnvelopeExponent_le {d m W : ℕ} (hd : 0 < d) :
    Nat.card
        {e : LocalVariable d →₀ ℕ // ContactEnvelopeExponent (d := d) m W e} ≤
      m * (m / d + 1) * (2 * m) * scaledExponentCount d (W + m) := by
  calc
    Nat.card
        {e : LocalVariable d →₀ ℕ // ContactEnvelopeExponent (d := d) m W e}
        ≤ Nat.card (ContactEnvelopeCode d m W) :=
      Nat.card_le_card_of_injective (encodeContactEnvelope hd)
        (encodeContactEnvelope_injective hd)
    _ = m * (m / d + 1) * (2 * m) * scaledExponentCount d (W + m) := by
      simp [ContactEnvelopeCode, scaledExponentCount, Nat.card_eq_fintype_card,
        mul_assoc]

/-- The contact-envelope monomial space has dimension no larger than the
cardinality of its explicit finite code. -/
theorem finrank_contactEnvelopeSpace_le
    {R : Type*} [Field R] {d m W : ℕ} (hd : 0 < d) :
    Module.finrank R (contactEnvelopeSpace (R := R) (d := d) m W) ≤
      m * (m / d + 1) * (2 * m) * scaledExponentCount d (W + m) := by
  let code :
      {e : LocalVariable d →₀ ℕ // ContactEnvelopeExponent (d := d) m W e} →
        ContactEnvelopeCode d m W := encodeContactEnvelope hd
  letI : Fintype
      {e : LocalVariable d →₀ ℕ // ContactEnvelopeExponent (d := d) m W e} :=
    Fintype.ofInjective code (by
      simpa [code] using encodeContactEnvelope_injective (m := m) (W := W) hd)
  let b : Module.Basis
      {e : LocalVariable d →₀ ℕ // ContactEnvelopeExponent (d := d) m W e}
      R (contactEnvelopeSpace (R := R) (d := d) m W) :=
    MvPolynomial.basisRestrictSupport R
      {e | ContactEnvelopeExponent (d := d) m W e}
  rw [Module.finrank_eq_card_basis b]
  simpa [Nat.card_eq_fintype_card] using
    (natCard_contactEnvelopeExponent_le (d := d) (m := m) (W := W) hd)

/-- With the manuscript's choice `m=d³`, the envelope dimension is at most
`4 d⁸ N(W+m) = 4 (m³/d) N(W+m)`.  The factor four is the harmless
fixed loss traded for avoiding the draft's complicated kernel subtraction. -/
theorem finrank_contactEnvelopeSpace_le_four_mul_d_pow_eight
    {R : Type*} [Field R] {d W : ℕ} (hd : 0 < d) :
    Module.finrank R
        (contactEnvelopeSpace (R := R) (d := d) (d ^ 3) W) ≤
      4 * d ^ 8 * scaledExponentCount d (W + d ^ 3) := by
  refine (finrank_contactEnvelopeSpace_le
    (R := R) (d := d) (m := d ^ 3) (W := W) hd).trans ?_
  have hdiv : d ^ 3 / d = d ^ 2 := by
    calc
      d ^ 3 / d = d * d ^ 2 / d := by
        congr 1
        ring
      _ = d ^ 2 := Nat.mul_div_right _ hd
  rw [hdiv]
  apply Nat.mul_le_mul_right
  have hpowers : d ^ 6 ≤ d ^ 8 :=
    Nat.pow_le_pow_right hd (by omega)
  calc
    d ^ 3 * (d ^ 2 + 1) * (2 * d ^ 3) =
        2 * d ^ 8 + 2 * d ^ 6 := by ring
    _ ≤ 2 * d ^ 8 + 2 * d ^ 8 :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 2 hpowers) _
    _ = 4 * d ^ 8 := by ring

end RSListDecoding
