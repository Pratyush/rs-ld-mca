import RSListDecoding.Lemmas.ScaledLattice
import RSListDecoding.Defs.LocalConstraints
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Algebra.Order.Floor.Div

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

/-- Triangular index set for pairs of nonnegative integers with sum below
`r`.  It is the exact shape left by the contact-order inequality after
splitting the `T` exponent modulo `d`. -/
abbrev ContactTriangle (r : ℕ) :=
  Σ z : Fin r, ↥(Finset.antidiagonal z.val)

theorem card_contactTriangle (r : ℕ) :
    Fintype.card (ContactTriangle r) = r * (r + 1) / 2 := by
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_coe, Finset.Nat.card_antidiagonal]
  rw [Fin.sum_univ_eq_sum_range (fun i => i + 1)]
  simp [Finset.sum_add_distrib, Finset.sum_range_id]
  rw [← Nat.choose_two_right r]
  have hrhs : r * (r + 1) / 2 = (r + 1).choose 2 := by
    simp [Nat.choose_two_right, Nat.mul_comm]
  rw [hrhs, Nat.choose_succ_succ']
  simp [Nat.choose_one_right, add_comm]

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

/-- Visible jet variables have contact weight zero, so contact order is
exactly the weighted sum of the `T` and `E` exponents. -/
theorem contactOrder_eq_t_add_d_mul_e {d : ℕ}
    (e : LocalVariable d →₀ ℕ) :
    contactOrder d e = e (localT d) + d * e (localE d) := by
  classical
  rw [contactOrder,
    Finsupp.sum_fintype _ _ (by
      intro v
      rcases v with (_ | (_ | j)) <;> simp),
    Fintype.sum_option, Fintype.sum_option]
  simp [contactWeight, localT, localE]

theorem coupledContactEnvelopeExponent_implies_contactEnvelopeExponent
    {d m W : ℕ} {e : LocalVariable d →₀ ℕ}
    (he : CoupledContactEnvelopeExponent (d := d) m W e) :
    ContactEnvelopeExponent (d := d) m W e := by
  rcases he with ⟨hcontact, hfirst, hhigher⟩
  have ht : e (localT d) ≤ contactOrder d e := by
    simpa [contactWeight, localT] using
      contactWeight_mul_exponent_le_contactOrder e (localT d)
  refine ⟨hcontact, ?_, ?_⟩ <;> omega

/-- The adaptive envelope is genuinely a subspace of the former uniform
envelope. -/
theorem coupledContactEnvelopeSpace_le_contactEnvelopeSpace
    {R : Type*} [CommRing R] {d : ℕ} (m W : ℕ) :
    coupledContactEnvelopeSpace (R := R) (d := d) m W ≤
      contactEnvelopeSpace (R := R) (d := d) m W := by
  intro F hF
  rw [coupledContactEnvelopeSpace, localExponentSpan,
    MvPolynomial.mem_restrictSupport_iff] at hF
  rw [contactEnvelopeSpace, localExponentSpan,
    MvPolynomial.mem_restrictSupport_iff]
  intro e he
  exact coupledContactEnvelopeExponent_implies_contactEnvelopeExponent (hF he)

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

/-- Sharper code at `m=d³`.  The first two contact coordinates occupy a
triangle, not the full rectangle used by `ContactEnvelopeCode`. -/
abbrev SharpContactEnvelopeCode (d W : ℕ) :=
  Fin d × ContactTriangle (d ^ 2) × Fin (2 * d ^ 3) ×
    BoundedScaledExponent d (W + d ^ 3)

/-- Exact triangular code for an arbitrary multiplicity divisible by the
derivative depth.  The quotient `m / d` is the side length of the
`(T / d,E)` triangle. -/
abbrev DivisibleContactEnvelopeCode (d m W : ℕ) :=
  Fin d × ContactTriangle (m / d) × Fin (2 * m) ×
    BoundedScaledExponent d (W + m)

/-- The exact pair of low-contact exponents `(T,E)`. -/
abbrev ContactLayer (d m : ℕ) :=
  {p : Fin m × Fin (m / d + 1) // p.1.val + d * p.2.val < m}

def contactLayerOrder {d m : ℕ} (p : ContactLayer d m) : ℕ :=
  p.1.1.val + d * p.1.2.val

/-- Dependent code for the coupled envelope.  At contact layer `(t,b)`,
the first-jet range has size `m+t+1`, while the higher-jet shell has its
actual budget `W+t+d*b`. -/
abbrev CoupledContactEnvelopeCode (d m W : ℕ) :=
  Σ p : ContactLayer d m,
    Fin (m + p.1.1.val + 1) ×
      BoundedScaledExponent d (W + contactLayerOrder p)

/-- Dependent finite code for the sharpened support envelope. -/
abbrev SharpenedContactEnvelopeCode (d m W : ℕ) :=
  Σ t : Fin m,
    Fin (min ((m - 1 - t.val) / d) t.val + 1) ×
      Fin (m + t.val + 1) × BoundedScaledExponent d (W + t.val)

/-- The exact weighted local-envelope sum. -/
def coupledContactEnvelopeCount (d m W : ℕ) : ℕ :=
  ∑ p : ContactLayer d m,
    (m + p.1.1.val + 1) *
      scaledExponentCount d (W + contactLayerOrder p)

/-- Exact cardinality bound for the strongest support-only local envelope. -/
def sharpenedContactEnvelopeCount (d m W : ℕ) : ℕ :=
  ∑ t : Fin m,
    (min ((m - 1 - t.val) / d) t.val + 1) * (m + t.val + 1) *
      scaledExponentCount d (W + t.val)

/-- The smallest `E` power used by the manuscript kernel in `T` layer
`r`.  This is `ceil((m-r)/d)`; it is kept as data for the remaining exact
quotient-rank formalization. -/
def paperKernelHeight (d m r : ℕ) : ℕ :=
  (m - r) ⌈/⌉ d

/-- The manuscript's kernel-subtracted coefficient in `T` layer `r`. -/
def paperLocalRankCoefficient (d m r : ℕ) : ℕ :=
  let h := paperKernelHeight d m r
  (r + 1) * (m + 1) - (r + 1 - h) * (m + 1 - h)

/-- Exact finite form of the local-rank upper bound from Lemmas 3.11--3.12
of the manuscript.  The definition is executable; proving that the
universal local map has rank at most this value remains a separate theorem
obligation. -/
def paperLocalRankCount (d m W : ℕ) : ℕ :=
  ∑ r : Fin m,
    paperLocalRankCoefficient d m r * scaledExponentCount d (W + r.val)

/-- Encode a contact-envelope monomial using the exact triangular
`(T / d,E)` region and the residue `T % d`. -/
def encodeContactEnvelopeSharp {d W : ℕ} (hd : 0 < d)
    (e : {e : LocalVariable d →₀ ℕ //
      ContactEnvelopeExponent (d := d) (d ^ 3) W e}) :
    SharpContactEnvelopeCode d W := by
  classical
  let t := e.1 (localT d)
  let b := e.1 (localE d)
  have hcontact : t + d * b < d ^ 3 := by
    simpa [t, b, contactOrder_eq_t_add_d_mul_e] using e.2.1
  have hquot : t / d + b < d ^ 2 := by
    have hdiv : (t + d * b) / d < d ^ 2 := by
      rw [Nat.div_lt_iff_lt_mul hd]
      nlinarith [hcontact]
    simpa using (Nat.add_mul_div_left t b hd) ▸ hdiv
  exact
    (⟨t % d, Nat.mod_lt _ hd⟩,
     ⟨⟨t / d + b, hquot⟩,
       ⟨(t / d, b), Finset.mem_antidiagonal.mpr rfl⟩⟩,
     ⟨localFirstJetExponent e.1, by
       have := e.2.2.1
       omega⟩,
     ⟨localHigherExponent e.1, by
       rw [mem_scaledExponentFinset, scaledWeight_localHigherExponent]
       exact e.2.2.2.trans (by omega)⟩)

/-- Encode a contact-envelope monomial into the exact triangular contact
region whenever the derivative depth divides the multiplicity. -/
def encodeContactEnvelopeDivisible {d m W : ℕ} (hd : 0 < d)
    (hdm : d ∣ m)
    (e : {e : LocalVariable d →₀ ℕ //
      ContactEnvelopeExponent (d := d) m W e}) :
    DivisibleContactEnvelopeCode d m W := by
  classical
  let t := e.1 (localT d)
  let b := e.1 (localE d)
  have hcontact : t + d * b < m := by
    simpa [t, b, contactOrder_eq_t_add_d_mul_e] using e.2.1
  have hdiv : (t + d * b) / d < m / d := by
    rw [Nat.div_lt_iff_lt_mul hd, Nat.div_mul_cancel hdm]
    exact hcontact
  have hquot : t / d + b < m / d := by
    simpa using (Nat.add_mul_div_left t b hd) ▸ hdiv
  exact
    (⟨t % d, Nat.mod_lt _ hd⟩,
     ⟨⟨t / d + b, hquot⟩,
       ⟨(t / d, b), Finset.mem_antidiagonal.mpr rfl⟩⟩,
     ⟨localFirstJetExponent e.1, by
       have := e.2.2.1
       omega⟩,
     ⟨localHigherExponent e.1, by
       rw [mem_scaledExponentFinset, scaledWeight_localHigherExponent]
       exact e.2.2.2.trans (by omega)⟩)

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

/-- Encode a monomial in the coupled envelope without replacing either
layer-dependent allowance by its maximum. -/
def encodeCoupledContactEnvelope {d m W : ℕ} (hd : 0 < d)
    (e : {e : LocalVariable d →₀ ℕ //
      CoupledContactEnvelopeExponent (d := d) m W e}) :
    CoupledContactEnvelopeCode d m W := by
  let t := e.1 (localT d)
  let b := e.1 (localE d)
  have hcontact : t + d * b < m := by
    simpa [t, b, contactOrder_eq_t_add_d_mul_e] using e.2.1
  let p : ContactLayer d m :=
    ⟨(⟨t, by omega⟩,
      ⟨b, Nat.lt_succ_of_le (localE_exponent_le_div hd e.1 e.2.1)⟩),
      hcontact⟩
  exact ⟨p,
    ⟨localFirstJetExponent e.1, by
      have hfirst := e.2.2.1
      dsimp [p, t]
      omega⟩,
    ⟨localHigherExponent e.1, by
      rw [mem_scaledExponentFinset, scaledWeight_localHigherExponent]
      have hhigher := e.2.2.2
      simpa [p, contactLayerOrder, t, b,
        contactOrder_eq_t_add_d_mul_e] using hhigher⟩⟩

/-- Encode a sharpened-envelope monomial without discarding either signed
invariant of the contact rewrite. -/
def encodeSharpenedContactEnvelope {d m W : ℕ} (hd : 0 < d)
    (e : {e : LocalVariable d →₀ ℕ //
      SharpenedContactEnvelopeExponent (d := d) m W e}) :
    SharpenedContactEnvelopeCode d m W := by
  let t := e.1 (localT d)
  let b := e.1 (localE d)
  have hcontact : t + d * b < m := by
    simpa [t, b, contactOrder_eq_t_add_d_mul_e] using e.2.1
  have ht : t < m := lt_of_le_of_lt (Nat.le_add_right t (d * b)) hcontact
  have hbdiv : b ≤ (m - 1 - t) / d := by
    rw [Nat.le_div_iff_mul_le hd]
    have : t + d * b ≤ m - 1 := by omega
    have hmul : b * d = d * b := Nat.mul_comm _ _
    omega
  exact
    ⟨⟨t, ht⟩,
     ⟨b, Nat.lt_succ_of_le (le_min hbdiv e.2.2.1)⟩,
     ⟨localFirstJetExponent e.1, Nat.lt_succ_of_le e.2.2.2.1⟩,
     ⟨localHigherExponent e.1, by
       rw [mem_scaledExponentFinset, scaledWeight_localHigherExponent]
       exact e.2.2.2.2⟩⟩

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

theorem encodeCoupledContactEnvelope_injective
    {d m W : ℕ} (hd : 0 < d) :
    Function.Injective (encodeCoupledContactEnvelope (m := m) (W := W) hd) := by
  intro e f hef
  have hT : e.1 (localT d) = f.1 (localT d) :=
    congrArg (fun z : CoupledContactEnvelopeCode d m W => z.1.1.1.val) hef
  have hE : e.1 (localE d) = f.1 (localE d) :=
    congrArg (fun z : CoupledContactEnvelopeCode d m W => z.1.1.2.val) hef
  have hfirst : localFirstJetExponent e.1 = localFirstJetExponent f.1 :=
    congrArg (fun z : CoupledContactEnvelopeCode d m W => z.2.1.val) hef
  have hhigher : localHigherExponent e.1 = localHigherExponent f.1 :=
    congrArg (fun z : CoupledContactEnvelopeCode d m W => z.2.2.1) hef
  apply Subtype.ext
  apply Finsupp.ext
  intro v
  rcases v with (_ | (_ | j))
  · exact hT
  · exact hE
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [localFirstJetExponent_eq, localY] using hfirst
    · exact congrFun hhigher i

theorem encodeSharpenedContactEnvelope_injective
    {d m W : ℕ} (hd : 0 < d) :
    Function.Injective
      (encodeSharpenedContactEnvelope (m := m) (W := W) hd) := by
  intro e f hef
  have hT : e.1 (localT d) = f.1 (localT d) :=
    congrArg (fun z : SharpenedContactEnvelopeCode d m W => z.1.val) hef
  have hE : e.1 (localE d) = f.1 (localE d) :=
    congrArg (fun z : SharpenedContactEnvelopeCode d m W => z.2.1.val) hef
  have hfirst : localFirstJetExponent e.1 = localFirstJetExponent f.1 :=
    congrArg (fun z : SharpenedContactEnvelopeCode d m W => z.2.2.1.val) hef
  have hhigher : localHigherExponent e.1 = localHigherExponent f.1 :=
    congrArg (fun z : SharpenedContactEnvelopeCode d m W => z.2.2.2.1) hef
  apply Subtype.ext
  apply Finsupp.ext
  intro v
  rcases v with (_ | (_ | j))
  · exact hT
  · exact hE
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [localFirstJetExponent_eq, localY] using hfirst
    · exact congrFun hhigher i

theorem card_coupledContactEnvelopeCode (d m W : ℕ) :
    Fintype.card (CoupledContactEnvelopeCode d m W) =
      coupledContactEnvelopeCount d m W := by
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  rfl

theorem card_sharpenedContactEnvelopeCode (d m W : ℕ) :
    Fintype.card (SharpenedContactEnvelopeCode d m W) =
      sharpenedContactEnvelopeCount d m W := by
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  simp [sharpenedContactEnvelopeCount, scaledExponentCount,
    mul_assoc]

theorem encodeContactEnvelopeSharp_injective {d W : ℕ} (hd : 0 < d) :
    Function.Injective (encodeContactEnvelopeSharp (W := W) hd) := by
  intro e f hef
  have hmod : e.1 (localT d) % d = f.1 (localT d) % d :=
    congrArg (fun z : SharpContactEnvelopeCode d W => z.1.val) hef
  have hquot : e.1 (localT d) / d = f.1 (localT d) / d :=
    congrArg (fun z : SharpContactEnvelopeCode d W => z.2.1.2.1.1) hef
  have hE : e.1 (localE d) = f.1 (localE d) :=
    congrArg (fun z : SharpContactEnvelopeCode d W => z.2.1.2.1.2) hef
  have hT : e.1 (localT d) = f.1 (localT d) := by
    calc
      e.1 (localT d) =
          d * (e.1 (localT d) / d) + e.1 (localT d) % d := by
            exact (Nat.div_add_mod _ _).symm
      _ = d * (f.1 (localT d) / d) + f.1 (localT d) % d := by
        rw [hquot, hmod]
      _ = f.1 (localT d) := Nat.div_add_mod _ _
  have hfirst := congrArg
    (fun z : SharpContactEnvelopeCode d W => z.2.2.1.val) hef
  have hhigher := congrArg
    (fun z : SharpContactEnvelopeCode d W => z.2.2.2.1) hef
  apply Subtype.ext
  apply Finsupp.ext
  intro v
  rcases v with (_ | (_ | j))
  · exact hT
  · exact hE
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [encodeContactEnvelopeSharp, localFirstJetExponent_eq,
        localY] using hfirst
    · exact congrFun hhigher i

theorem encodeContactEnvelopeDivisible_injective
    {d m W : ℕ} (hd : 0 < d) (hdm : d ∣ m) :
    Function.Injective
      (encodeContactEnvelopeDivisible (m := m) (W := W) hd hdm) := by
  intro e f hef
  have hmod : e.1 (localT d) % d = f.1 (localT d) % d :=
    congrArg (fun z : DivisibleContactEnvelopeCode d m W => z.1.val) hef
  have hquot : e.1 (localT d) / d = f.1 (localT d) / d :=
    congrArg
      (fun z : DivisibleContactEnvelopeCode d m W => z.2.1.2.1.1) hef
  have hE : e.1 (localE d) = f.1 (localE d) :=
    congrArg
      (fun z : DivisibleContactEnvelopeCode d m W => z.2.1.2.1.2) hef
  have hT : e.1 (localT d) = f.1 (localT d) := by
    calc
      e.1 (localT d) =
          d * (e.1 (localT d) / d) + e.1 (localT d) % d := by
            exact (Nat.div_add_mod _ _).symm
      _ = d * (f.1 (localT d) / d) + f.1 (localT d) % d := by
        rw [hquot, hmod]
      _ = f.1 (localT d) := Nat.div_add_mod _ _
  have hfirst := congrArg
    (fun z : DivisibleContactEnvelopeCode d m W => z.2.2.1.val) hef
  have hhigher := congrArg
    (fun z : DivisibleContactEnvelopeCode d m W => z.2.2.2.1) hef
  apply Subtype.ext
  apply Finsupp.ext
  intro v
  rcases v with (_ | (_ | j))
  · exact hT
  · exact hE
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [encodeContactEnvelopeDivisible, localFirstJetExponent_eq,
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

/-- Exact contact-layer-adaptive count. -/
theorem natCard_coupledContactEnvelopeExponent_le
    {d m W : ℕ} (hd : 0 < d) :
    Nat.card
        {e : LocalVariable d →₀ ℕ //
          CoupledContactEnvelopeExponent (d := d) m W e} ≤
      coupledContactEnvelopeCount d m W := by
  calc
    Nat.card
        {e : LocalVariable d →₀ ℕ //
          CoupledContactEnvelopeExponent (d := d) m W e}
        ≤ Nat.card (CoupledContactEnvelopeCode d m W) :=
      Nat.card_le_card_of_injective (encodeCoupledContactEnvelope hd)
        (encodeCoupledContactEnvelope_injective hd)
    _ = coupledContactEnvelopeCount d m W := by
      rw [Nat.card_eq_fintype_card, card_coupledContactEnvelopeCode]

theorem natCard_sharpenedContactEnvelopeExponent_le
    {d m W : ℕ} (hd : 0 < d) :
    Nat.card
        {e : LocalVariable d →₀ ℕ //
          SharpenedContactEnvelopeExponent (d := d) m W e} ≤
      sharpenedContactEnvelopeCount d m W := by
  let code :
      {e : LocalVariable d →₀ ℕ //
        SharpenedContactEnvelopeExponent (d := d) m W e} →
        SharpenedContactEnvelopeCode d m W :=
    encodeSharpenedContactEnvelope hd
  calc
    Nat.card
        {e : LocalVariable d →₀ ℕ //
          SharpenedContactEnvelopeExponent (d := d) m W e}
        ≤ Nat.card (SharpenedContactEnvelopeCode d m W) :=
      Nat.card_le_card_of_injective code
        (encodeSharpenedContactEnvelope_injective hd)
    _ = sharpenedContactEnvelopeCount d m W := by
      rw [Nat.card_eq_fintype_card, card_sharpenedContactEnvelopeCode]

/-- Exact triangular contact count for every multiplicity divisible by the
derivative depth.  This removes the factor two in the generic rectangular
bound. -/
theorem natCard_contactEnvelopeExponent_le_divisible
    {d m W : ℕ} (hd : 0 < d) (hdm : d ∣ m) :
    Nat.card
        {e : LocalVariable d →₀ ℕ //
          ContactEnvelopeExponent (d := d) m W e} ≤
      m * (m / d + 1) * m * scaledExponentCount d (W + m) := by
  have heven : 2 ∣ (m / d) * (m / d + 1) := by
    exact (Nat.even_mul_succ_self (m / d)).two_dvd
  have hcancel :
      ((m / d) * (m / d + 1) / 2) * 2 =
        (m / d) * (m / d + 1) := Nat.div_mul_cancel heven
  have hmuldiv : d * (m / d) = m := Nat.mul_div_cancel' hdm
  calc
    Nat.card
        {e : LocalVariable d →₀ ℕ //
          ContactEnvelopeExponent (d := d) m W e}
        ≤ Nat.card (DivisibleContactEnvelopeCode d m W) :=
      Nat.card_le_card_of_injective
        (encodeContactEnvelopeDivisible hd hdm)
        (encodeContactEnvelopeDivisible_injective hd hdm)
    _ = d * ((m / d) * (m / d + 1) / 2) * (2 * m) *
          scaledExponentCount d (W + m) := by
      rw [Nat.card_eq_fintype_card]
      change Fintype.card
          (Fin d × ContactTriangle (m / d) × Fin (2 * m) ×
            BoundedScaledExponent d (W + m)) = _
      simp only [Fintype.card_prod, Fintype.card_fin, card_contactTriangle,
        Fintype.card_coe]
      simp [scaledExponentCount, mul_assoc]
    _ = m * (m / d + 1) * m *
          scaledExponentCount d (W + m) := by
      rw [show d * ((m / d) * (m / d + 1) / 2) * (2 * m) =
          d * (((m / d) * (m / d + 1) / 2) * 2) * m by ring,
        hcancel, ← mul_assoc, hmuldiv]

/-- Exact triangular encoding improves the direct local-rank factor
`4d⁸` to `d⁸+d⁶`, whose asymptotic leading constant is one. -/
theorem natCard_contactEnvelopeExponent_le_exact
    {d W : ℕ} (hd : 0 < d) :
    Nat.card
        {e : LocalVariable d →₀ ℕ //
          ContactEnvelopeExponent (d := d) (d ^ 3) W e} ≤
      (d ^ 8 + d ^ 6) * scaledExponentCount d (W + d ^ 3) := by
  have heven : 2 ∣ (d ^ 2) * (d ^ 2 + 1) := by
    exact (Nat.even_mul_succ_self (d ^ 2)).two_dvd
  have hcancel :
      ((d ^ 2) * (d ^ 2 + 1) / 2) * 2 =
        (d ^ 2) * (d ^ 2 + 1) := Nat.div_mul_cancel heven
  calc
    Nat.card
        {e : LocalVariable d →₀ ℕ //
          ContactEnvelopeExponent (d := d) (d ^ 3) W e}
        ≤ Nat.card (SharpContactEnvelopeCode d W) :=
      Nat.card_le_card_of_injective (encodeContactEnvelopeSharp hd)
        (encodeContactEnvelopeSharp_injective hd)
    _ = d * ((d ^ 2) * (d ^ 2 + 1) / 2) * (2 * d ^ 3) *
          scaledExponentCount d (W + d ^ 3) := by
      rw [Nat.card_eq_fintype_card]
      change Fintype.card
          (Fin d × ContactTriangle (d ^ 2) × Fin (2 * d ^ 3) ×
            BoundedScaledExponent d (W + d ^ 3)) = _
      simp only [Fintype.card_prod, Fintype.card_fin, card_contactTriangle,
        Fintype.card_coe]
      simp [scaledExponentCount, mul_assoc]
    _ = (d ^ 8 + d ^ 6) *
          scaledExponentCount d (W + d ^ 3) := by
      rw [show d * ((d ^ 2) * (d ^ 2 + 1) / 2) * (2 * d ^ 3) =
          d * (((d ^ 2) * (d ^ 2 + 1) / 2) * 2) * d ^ 3 by ring,
        hcancel]
      ring

theorem natCard_contactEnvelopeExponent_le_two_mul_d_pow_eight
    {d W : ℕ} (hd : 0 < d) :
    Nat.card
        {e : LocalVariable d →₀ ℕ //
          ContactEnvelopeExponent (d := d) (d ^ 3) W e} ≤
      2 * d ^ 8 * scaledExponentCount d (W + d ^ 3) := by
  have hr1 : 1 ≤ d ^ 2 := by
    have : 0 < d ^ 2 := pow_pos hd _
    omega
  have htri :
      (d ^ 2) * (d ^ 2 + 1) / 2 ≤ (d ^ 2) ^ 2 := by
    apply Nat.div_le_of_le_mul
    have hlinear : d ^ 2 + 1 ≤ 2 * d ^ 2 := by omega
    have hmul := Nat.mul_le_mul_left (d ^ 2) hlinear
    nlinarith
  calc
    Nat.card
        {e : LocalVariable d →₀ ℕ //
          ContactEnvelopeExponent (d := d) (d ^ 3) W e}
        ≤ Nat.card (SharpContactEnvelopeCode d W) :=
      Nat.card_le_card_of_injective (encodeContactEnvelopeSharp hd)
        (encodeContactEnvelopeSharp_injective hd)
    _ = d * ((d ^ 2) * (d ^ 2 + 1) / 2) * (2 * d ^ 3) *
          scaledExponentCount d (W + d ^ 3) := by
      rw [Nat.card_eq_fintype_card]
      change Fintype.card
          (Fin d × ContactTriangle (d ^ 2) × Fin (2 * d ^ 3) ×
            BoundedScaledExponent d (W + d ^ 3)) = _
      simp only [Fintype.card_prod, Fintype.card_fin, card_contactTriangle,
        Fintype.card_coe]
      simp [scaledExponentCount, mul_assoc]
    _ ≤ d * (d ^ 2) ^ 2 * (2 * d ^ 3) *
          scaledExponentCount d (W + d ^ 3) := by gcongr
    _ = 2 * d ^ 8 * scaledExponentCount d (W + d ^ 3) := by ring

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

/-- Rank bound retaining the exact contact-layer weighted sum. -/
theorem finrank_coupledContactEnvelopeSpace_le
    {R : Type*} [Field R] {d m W : ℕ} (hd : 0 < d) :
    Module.finrank R
        (coupledContactEnvelopeSpace (R := R) (d := d) m W) ≤
      coupledContactEnvelopeCount d m W := by
  let code :
      {e : LocalVariable d →₀ ℕ //
        CoupledContactEnvelopeExponent (d := d) m W e} →
        CoupledContactEnvelopeCode d m W :=
    encodeCoupledContactEnvelope hd
  letI : Fintype
      {e : LocalVariable d →₀ ℕ //
        CoupledContactEnvelopeExponent (d := d) m W e} :=
    Fintype.ofInjective code (by
      simpa [code] using
        encodeCoupledContactEnvelope_injective (m := m) (W := W) hd)
  let b : Module.Basis
      {e : LocalVariable d →₀ ℕ //
        CoupledContactEnvelopeExponent (d := d) m W e}
      R (coupledContactEnvelopeSpace (R := R) (d := d) m W) :=
    MvPolynomial.basisRestrictSupport R
      {e | CoupledContactEnvelopeExponent (d := d) m W e}
  rw [Module.finrank_eq_card_basis b]
  simpa [Nat.card_eq_fintype_card] using
    (natCard_coupledContactEnvelopeExponent_le
      (d := d) (m := m) (W := W) hd)

/-- Exact dimension bound for the strongest support-only local codomain. -/
theorem finrank_sharpenedContactEnvelopeSpace_le
    {R : Type*} [Field R] {d m W : ℕ} (hd : 0 < d) :
    Module.finrank R
        (sharpenedContactEnvelopeSpace (R := R) (d := d) m W) ≤
      sharpenedContactEnvelopeCount d m W := by
  let code :
      {e : LocalVariable d →₀ ℕ //
        SharpenedContactEnvelopeExponent (d := d) m W e} →
        SharpenedContactEnvelopeCode d m W :=
    encodeSharpenedContactEnvelope hd
  letI : Fintype
      {e : LocalVariable d →₀ ℕ //
        SharpenedContactEnvelopeExponent (d := d) m W e} :=
    Fintype.ofInjective code (by
      simpa [code] using
        encodeSharpenedContactEnvelope_injective (m := m) (W := W) hd)
  let b : Module.Basis
      {e : LocalVariable d →₀ ℕ //
        SharpenedContactEnvelopeExponent (d := d) m W e}
      R (sharpenedContactEnvelopeSpace (R := R) (d := d) m W) :=
    MvPolynomial.basisRestrictSupport R
      {e | SharpenedContactEnvelopeExponent (d := d) m W e}
  rw [Module.finrank_eq_card_basis b]
  simpa [Nat.card_eq_fintype_card] using
    (natCard_sharpenedContactEnvelopeExponent_le
      (d := d) (m := m) (W := W) hd)

/-- Exact generic local-rank bound when `d ∣ m`.  It is pointwise half the
older rectangular estimate. -/
theorem finrank_contactEnvelopeSpace_le_divisible
    {R : Type*} [Field R] {d m W : ℕ} (hd : 0 < d) (hdm : d ∣ m) :
    Module.finrank R (contactEnvelopeSpace (R := R) (d := d) m W) ≤
      m * (m / d + 1) * m * scaledExponentCount d (W + m) := by
  let code :
      {e : LocalVariable d →₀ ℕ //
        ContactEnvelopeExponent (d := d) m W e} →
        DivisibleContactEnvelopeCode d m W :=
    encodeContactEnvelopeDivisible hd hdm
  letI : Fintype
      {e : LocalVariable d →₀ ℕ //
        ContactEnvelopeExponent (d := d) m W e} :=
    Fintype.ofInjective code (by
      simpa [code] using
        encodeContactEnvelopeDivisible_injective (m := m) (W := W) hd hdm)
  let b : Module.Basis
      {e : LocalVariable d →₀ ℕ //
        ContactEnvelopeExponent (d := d) m W e}
      R (contactEnvelopeSpace (R := R) (d := d) m W) :=
    MvPolynomial.basisRestrictSupport R
      {e | ContactEnvelopeExponent (d := d) m W e}
  rw [Module.finrank_eq_card_basis b]
  simpa [Nat.card_eq_fintype_card] using
    (natCard_contactEnvelopeExponent_le_divisible
      (d := d) (m := m) (W := W) hd hdm)

/-- Sharp local-rank bound using the triangular contact encoding. -/
theorem finrank_contactEnvelopeSpace_le_two_mul_d_pow_eight
    {R : Type*} [Field R] {d W : ℕ} (hd : 0 < d) :
    Module.finrank R
        (contactEnvelopeSpace (R := R) (d := d) (d ^ 3) W) ≤
      2 * d ^ 8 * scaledExponentCount d (W + d ^ 3) := by
  let code :
      {e : LocalVariable d →₀ ℕ //
        ContactEnvelopeExponent (d := d) (d ^ 3) W e} →
        SharpContactEnvelopeCode d W := encodeContactEnvelopeSharp hd
  letI : Fintype
      {e : LocalVariable d →₀ ℕ //
        ContactEnvelopeExponent (d := d) (d ^ 3) W e} :=
    Fintype.ofInjective code (by
      simpa [code] using encodeContactEnvelopeSharp_injective (W := W) hd)
  let b : Module.Basis
      {e : LocalVariable d →₀ ℕ //
        ContactEnvelopeExponent (d := d) (d ^ 3) W e}
      R (contactEnvelopeSpace (R := R) (d := d) (d ^ 3) W) :=
    MvPolynomial.basisRestrictSupport R
      {e | ContactEnvelopeExponent (d := d) (d ^ 3) W e}
  rw [Module.finrank_eq_card_basis b]
  simpa [Nat.card_eq_fintype_card] using
    (natCard_contactEnvelopeExponent_le_two_mul_d_pow_eight
      (d := d) (W := W) hd)

/-- Exact local-rank bound furnished by the triangular encoding. -/
theorem finrank_contactEnvelopeSpace_le_exact
    {R : Type*} [Field R] {d W : ℕ} (hd : 0 < d) :
    Module.finrank R
        (contactEnvelopeSpace (R := R) (d := d) (d ^ 3) W) ≤
      (d ^ 8 + d ^ 6) * scaledExponentCount d (W + d ^ 3) := by
  let code :
      {e : LocalVariable d →₀ ℕ //
        ContactEnvelopeExponent (d := d) (d ^ 3) W e} →
        SharpContactEnvelopeCode d W := encodeContactEnvelopeSharp hd
  letI : Fintype
      {e : LocalVariable d →₀ ℕ //
        ContactEnvelopeExponent (d := d) (d ^ 3) W e} :=
    Fintype.ofInjective code (by
      simpa [code] using encodeContactEnvelopeSharp_injective (W := W) hd)
  let b : Module.Basis
      {e : LocalVariable d →₀ ℕ //
        ContactEnvelopeExponent (d := d) (d ^ 3) W e}
      R (contactEnvelopeSpace (R := R) (d := d) (d ^ 3) W) :=
    MvPolynomial.basisRestrictSupport R
      {e | ContactEnvelopeExponent (d := d) (d ^ 3) W e}
  rw [Module.finrank_eq_card_basis b]
  simpa [Nat.card_eq_fintype_card] using
    (natCard_contactEnvelopeExponent_le_exact (d := d) (W := W) hd)

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
