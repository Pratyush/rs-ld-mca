import RSListDecoding.Lemmas.AlgorithmicDecoder
import Mathlib.Tactic

/-!
# Finite-field operation bounds

This file converts the exact decoder cost into a uniform power of `q`.  The
counting estimates are intentionally coarse: their purpose is to make every
dependence explicit and auditable, not to optimize constants.
-/

noncomputable section

open scoped BigOperators

namespace RSListDecoding

/-- The anisotropic simplex is contained in its defining coordinate box. -/
theorem scaledExponentCount_le_box (d z : ℕ) :
    scaledExponentCount d z ≤ (z + 1) ^ (d - 1) := by
  calc
    scaledExponentCount d z ≤ (scaledExponentBox d z).card := by
      exact Finset.card_filter_le _ _
    _ = (z + 1) ^ (d - 1) := by
      simp [scaledExponentBox]

/-- Encode one global monomial exponent in a rectangular coordinate box. -/
def encodeInterpolationColumn {d m A K B W C : ℕ}
    (u : InterpolationColumn d m A K B W C) :
    (JetVariable d → Fin (m * A + B + 1)) :=
  fun v ↦ ⟨u.1 v, by
    have huFinset : u.1 ∈ globalEligibleExponents d m A K B W C := u.2
    have hu : GlobalEligibleExponent d m A K B W C u.1 :=
      mem_globalEligibleExponents.mp huFinset
    have hx : u.1 none < m * A :=
      lt_of_le_of_lt
        (Nat.le_add_right (u.1 none) ((K - 1) * totalJetDegree u.1))
        hu.2.2.1
    have hdegree : Finsupp.degree u.1 ≤ m * A + B := by
      rw [exponentDegree_eq_x_add_totalJetDegree]
      exact Nat.add_le_add (Nat.le_of_lt hx) hu.2.1
    exact Nat.lt_succ_of_le ((Finsupp.le_degree v u.1).trans hdegree)⟩

theorem encodeInterpolationColumn_injective {d m A K B W C : ℕ} :
    Function.Injective
      (encodeInterpolationColumn (d := d) (m := m) (A := A)
        (K := K) (B := B) (W := W) (C := C)) := by
  intro u v huv
  apply Subtype.ext
  apply Finsupp.ext
  intro x
  exact congrArg Fin.val (congrFun huv x)

/-- Rectangular upper bound for the number of eligible interpolation
monomials. -/
theorem natCard_interpolationColumn_le (d m A K B W C : ℕ) :
    Nat.card (InterpolationColumn d m A K B W C) ≤
      (m * A + B + 1) ^ (d + 2) := by
  calc
    Nat.card (InterpolationColumn d m A K B W C) ≤
        Nat.card (JetVariable d → Fin (m * A + B + 1)) :=
      Nat.card_le_card_of_injective encodeInterpolationColumn
        encodeInterpolationColumn_injective
    _ = (m * A + B + 1) ^ (d + 2) := by
      rw [Nat.card_fun]
      simp [JetVariable, Nat.card_eq_fintype_card]

/-- The rounded anisotropic budget has the simple polynomial upper bound
`W ≤ 2d⁴` in the scoped parameter range. -/
theorem interpolationWeightBudget_le_two_mul_derivativeOrder_pow_four
    {ε θ : ℝ} (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hd : 0 < derivativeOrder ε θ) :
    interpolationWeightBudget ε θ ≤ 2 * derivativeOrder ε θ ^ 4 := by
  let d := derivativeOrder ε θ
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
  have hden : 1 ≤ 1 + Real.log (d : ℝ) := by linarith
  have hfactor : 0 ≤ 1 + θ / 2 := by linarith
  have hnum :
      0 ≤ (1 + θ / 2) * (d : ℝ) * (multiplicity ε θ : ℝ) := by
    positivity
  have hfloor :
      (interpolationWeightBudget ε θ : ℝ) ≤
        ((1 + θ / 2) * (d : ℝ) * (multiplicity ε θ : ℝ)) /
          (1 + Real.log (d : ℝ)) := by
    rw [interpolationWeightBudget]
    exact Nat.floor_le (div_nonneg hnum (by linarith))
  have hdivide :
      ((1 + θ / 2) * (d : ℝ) * (multiplicity ε θ : ℝ)) /
          (1 + Real.log (d : ℝ)) ≤
        (1 + θ / 2) * (d : ℝ) * (multiplicity ε θ : ℝ) := by
    exact div_le_self hnum hden
  have hfactor2 : 1 + θ / 2 ≤ 2 := by linarith
  have hreal :
      (interpolationWeightBudget ε θ : ℝ) ≤
        (2 * d ^ 4 : ℕ) := by
    calc
      (interpolationWeightBudget ε θ : ℝ) ≤ _ := hfloor
      _ ≤ (1 + θ / 2) * (d : ℝ) * (multiplicity ε θ : ℝ) := hdivide
      _ ≤ 2 * (d : ℝ) * (multiplicity ε θ : ℝ) := by gcongr
      _ = (2 * d ^ 4 : ℕ) := by
        simp [d, multiplicity]
        ring
  exact_mod_cast hreal

/-- Eligible global monomials occupy at most `q^(3(d+2))` columns under the
public field-size hypotheses. -/
theorem natCard_interpolationColumn_le_q_pow
    {q d m A K B W C : ℕ} (hq : Nat.Prime q) (_hdq : d < q)
    (hBq : B < q) (hmAq : m * A ≤ q ^ 2) :
    Nat.card (InterpolationColumn d m A K B W C) ≤
      q ^ (3 * (d + 2)) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hbase : m * A + B + 1 ≤ q ^ 3 := by
    calc
      m * A + B + 1 ≤ q ^ 2 + q := by omega
      _ ≤ q ^ 2 + q ^ 2 := by
        gcongr
        exact (Nat.le_mul_of_pos_left q (by omega)).trans_eq (pow_two q).symm
      _ = 2 * q ^ 2 := by ring
      _ ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq2
      _ = q ^ 3 := by ring
  calc
    Nat.card (InterpolationColumn d m A K B W C) ≤
        (m * A + B + 1) ^ (d + 2) :=
      natCard_interpolationColumn_le d m A K B W C
    _ ≤ (q ^ 3) ^ (d + 2) := Nat.pow_le_pow_left hbase _
    _ = q ^ (3 * (d + 2)) := (pow_mul q 3 (d + 2)).symm

/-- Contact-envelope coordinates occupy at most the displayed `q`-power at
the rounded multiplicity and anisotropic budget. -/
theorem natCard_scopedContactEnvelope_le_q_pow
    {q d W : ℕ} (hq : Nat.Prime q) (hd : 0 < d) (hdq : d < q)
    (hW : W ≤ 2 * d ^ 4) :
    Nat.card (ContactEnvelopeCoordinate d (d ^ 3) W) ≤
      q ^ (6 * (d - 1) + 9) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hdle : d ≤ q := hdq.le
  have hd3 : d ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hdle _
  have hd4 : d ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hdle _
  have hdiv : d ^ 3 / d = d ^ 2 := by
    calc
      d ^ 3 / d = d * d ^ 2 / d := by congr 1; ring
      _ = d ^ 2 := Nat.mul_div_right _ hd
  have hsecond : d ^ 2 + 1 ≤ q ^ 2 := by
    have hdlt2 : d ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hdq (by omega)
    omega
  have hthird : 2 * d ^ 3 ≤ q ^ 4 := by
    calc
      2 * d ^ 3 ≤ 2 * q ^ 3 := Nat.mul_le_mul_left 2 hd3
      _ ≤ q * q ^ 3 := Nat.mul_le_mul_right _ hq2
      _ = q ^ 4 := by ring
  have hq4pos : 1 ≤ q ^ 4 := by
    have : 0 < q ^ 4 := pow_pos hq.pos _
    omega
  have hbase : W + d ^ 3 + 1 ≤ q ^ 6 := by
    calc
      W + d ^ 3 + 1 ≤ 2 * d ^ 4 + d ^ 3 + 1 := by omega
      _ ≤ 2 * q ^ 4 + q ^ 4 + q ^ 4 := by omega
      _ = 4 * q ^ 4 := by ring
      _ ≤ q ^ 2 * q ^ 4 := by
        gcongr
        nlinarith
      _ = q ^ 6 := by ring
  have hcount : scaledExponentCount d (W + d ^ 3) ≤
      q ^ (6 * (d - 1)) := by
    calc
      scaledExponentCount d (W + d ^ 3) ≤
          (W + d ^ 3 + 1) ^ (d - 1) :=
        scaledExponentCount_le_box d (W + d ^ 3)
      _ ≤ (q ^ 6) ^ (d - 1) := Nat.pow_le_pow_left hbase _
      _ = q ^ (6 * (d - 1)) := (pow_mul q 6 (d - 1)).symm
  have hraw := natCard_contactEnvelopeExponent_le
    (d := d) (m := d ^ 3) (W := W) hd
  rw [hdiv] at hraw
  calc
    Nat.card (ContactEnvelopeCoordinate d (d ^ 3) W) ≤
        d ^ 3 * (d ^ 2 + 1) * (2 * d ^ 3) *
          scaledExponentCount d (W + d ^ 3) := hraw
    _ ≤ q ^ 3 * q ^ 2 * q ^ 4 * q ^ (6 * (d - 1)) := by
      gcongr
    _ = q ^ (6 * (d - 1) + 9) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega

/-- The explicit per-entry construction allowance is itself a small
`q`-power. -/
theorem interpolationEntryOperations_le_q_pow
    {q d m A B : ℕ} (hq : Nat.Prime q) (hdq : d < q)
    (hBq : B < q) (hmAq : m * A ≤ q ^ 2) :
    interpolationEntryOperations d m A B ≤ q ^ (2 * d + 15) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hma1 : m * A + 1 ≤ q ^ 3 := by
    calc
      m * A + 1 ≤ q ^ 2 + 1 := by omega
      _ ≤ q ^ 2 + q ^ 2 := by
        have : 1 ≤ q ^ 2 := by nlinarith
        omega
      _ = 2 * q ^ 2 := by ring
      _ ≤ q * q ^ 2 := Nat.mul_le_mul_right _ hq2
      _ = q ^ 3 := by ring
  have hmiddle : B + d + 2 ≤ q ^ 2 := by
    have : B + d + 2 ≤ 2 * q := by omega
    calc
      B + d + 2 ≤ 2 * q := this
      _ ≤ q * q := Nat.mul_le_mul_right q hq2
      _ = q ^ 2 := by ring
  have hlast : m * A + B + d + 3 ≤ q ^ 4 := by
    have hpre : m * A + B + d + 3 ≤ q ^ 2 + 2 * q + 1 := by omega
    calc
      m * A + B + d + 3 ≤ q ^ 2 + 2 * q + 1 := hpre
      _ = (q + 1) ^ 2 := by ring
      _ ≤ (q ^ 2) ^ 2 := by
        apply Nat.pow_le_pow_left _ _
        nlinarith
      _ = q ^ 4 := by ring
  rw [interpolationEntryOperations]
  calc
    (m * A + 1) * (B + d + 2) ^ (d + 2) *
          (m * A + B + d + 3) ^ 2 ≤
        q ^ 3 * (q ^ 2) ^ (d + 2) * (q ^ 4) ^ 2 := by
      gcongr
    _ = q ^ (2 * d + 15) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega

/-- The full row set (one contact-envelope block per received point) has the
displayed coarse q-power size. -/
theorem interpolationRowCount_le_q_pow
    {q n d W : ℕ} (hq : Nat.Prime q) (hd : 0 < d) (hdq : d < q)
    (hnq : n ≤ q) (hW : W ≤ 2 * d ^ 4) :
    n * Nat.card (ContactEnvelopeCoordinate d (d ^ 3) W) ≤
      q ^ (6 * (d - 1) + 10) := by
  have hcontact :=
    natCard_scopedContactEnvelope_le_q_pow hq hd hdq hW
  calc
    n * Nat.card (ContactEnvelopeCoordinate d (d ^ 3) W) ≤
        q * q ^ (6 * (d - 1) + 9) := Nat.mul_le_mul hnq hcontact
    _ = q ^ (6 * (d - 1) + 10) := by
      rw [← pow_succ']

/-- Cost of explicitly constructing the full interpolation matrix. -/
theorem interpolationMatrixOperationsFull_le_q_pow
    {q n d A K B W C : ℕ}
    (hq : Nat.Prime q) (hd : 0 < d) (hdq : d < q)
    (hnq : n ≤ q) (hBq : B < q) (hmAq : d ^ 3 * A ≤ q ^ 2)
    (hW : W ≤ 2 * d ^ 4) :
    interpolationMatrixOperationsFull n d (d ^ 3) A K B W C ≤
      q ^ (11 * d + 25) := by
  have hrows := interpolationRowCount_le_q_pow hq hd hdq hnq hW
  have hcols := natCard_interpolationColumn_le_q_pow
    (K := K) (W := W) (C := C) hq hdq hBq hmAq
  have hentry :=
    interpolationEntryOperations_le_q_pow hq hdq hBq hmAq
  calc
    interpolationMatrixOperationsFull n d (d ^ 3) A K B W C =
        (n * Nat.card (ContactEnvelopeCoordinate d (d ^ 3) W)) *
          Nat.card (InterpolationColumn d (d ^ 3) A K B W C) *
            interpolationEntryOperations d (d ^ 3) A B := rfl
    _ ≤ q ^ (6 * (d - 1) + 10) * q ^ (3 * (d + 2)) *
          q ^ (2 * d + 15) := by gcongr
    _ = q ^ ((6 * (d - 1) + 10) + 3 * (d + 2) + (2 * d + 15)) := by
      rw [← pow_add, ← pow_add]
    _ = q ^ (11 * d + 25) := by
      congr 1
      omega

/-- Cost of the checked Gaussian-elimination phase. -/
theorem interpolationGaussianOperations_le_q_pow
    {q n d A K B W C : ℕ}
    (hq : Nat.Prime q) (hd : 0 < d) (hdq : d < q)
    (hnq : n ≤ q) (hBq : B < q) (hmAq : d ^ 3 * A ≤ q ^ 2)
    (hW : W ≤ 2 * d ^ 4) :
    8 * (n * Nat.card (ContactEnvelopeCoordinate d (d ^ 3) W)) *
          Nat.card (InterpolationColumn d (d ^ 3) A K B W C) ^ 2 +
        Nat.card (InterpolationColumn d (d ^ 3) A K B W C) ≤
      q ^ (12 * d + 20) := by
  have hq2 : 2 ≤ q := hq.two_le
  have h8 : 8 ≤ q ^ 3 := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 _
  have hrows := interpolationRowCount_le_q_pow hq hd hdq hnq hW
  have hcols := natCard_interpolationColumn_le_q_pow
    (K := K) (W := W) (C := C) hq hdq hBq hmAq
  have hfirst :
      8 * (n * Nat.card (ContactEnvelopeCoordinate d (d ^ 3) W)) *
          Nat.card (InterpolationColumn d (d ^ 3) A K B W C) ^ 2 ≤
        q ^ (12 * d + 19) := by
    calc
      8 * (n * Nat.card (ContactEnvelopeCoordinate d (d ^ 3) W)) *
            Nat.card (InterpolationColumn d (d ^ 3) A K B W C) ^ 2 ≤
          q ^ 3 * q ^ (6 * (d - 1) + 10) *
            (q ^ (3 * (d + 2))) ^ 2 := by gcongr
      _ = q ^ (3 + (6 * (d - 1) + 10) + 3 * (d + 2) * 2) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
      _ = q ^ (12 * d + 19) := by
        congr 1
        omega
  have hcols' :
      Nat.card (InterpolationColumn d (d ^ 3) A K B W C) ≤
        q ^ (12 * d + 19) :=
    hcols.trans (Nat.pow_le_pow_right hq.pos (by omega))
  calc
    8 * (n * Nat.card (ContactEnvelopeCoordinate d (d ^ 3) W)) *
          Nat.card (InterpolationColumn d (d ^ 3) A K B W C) ^ 2 +
        Nat.card (InterpolationColumn d (d ^ 3) A K B W C) ≤
      q ^ (12 * d + 19) + q ^ (12 * d + 19) :=
        Nat.add_le_add hfirst hcols'
    _ = 2 * q ^ (12 * d + 19) := by ring
    _ ≤ q * q ^ (12 * d + 19) := Nat.mul_le_mul_right _ hq2
    _ = q ^ (12 * d + 20) := by
      rw [← pow_succ']

/-- The direct subcode-and-agreement filter has polynomial cost in q. -/
theorem candidateFilterOperations_le_q_pow
    {q n K : ℕ} (hq : Nat.Prime q) (hKn : K < n) (hnq : n ≤ q) :
    candidateFilterOperations n K ≤ q ^ 4 := by
  have hq2 : 2 ≤ q := hq.two_le
  have hKq : K + 1 ≤ q := by omega
  have hsquare : K ^ 2 + 2 * K + 1 ≤ q ^ 2 := by
    calc
      K ^ 2 + 2 * K + 1 = (K + 1) ^ 2 := by ring
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hKq _
  have hqle3 : q ≤ q ^ 3 := by
    simpa using Nat.pow_le_pow_right hq.pos (by omega : 1 ≤ 3)
  rw [candidateFilterOperations]
  calc
    K + n * (K ^ 2 + 2 * K + 1) ≤ q + q * q ^ 2 := by
      gcongr
      omega
    _ = q + q ^ 3 := by ring
    _ ≤ q ^ 3 + q ^ 3 := Nat.add_le_add_right hqle3 _
    _ = 2 * q ^ 3 := by ring
    _ ≤ q * q ^ 3 := Nat.mul_le_mul_right _ hq2
    _ = q ^ 4 := by ring

/-- A single explicit finite-field-operation bound for the fixed-parameter
decoder.  The constant 34 is deliberately generous; optimizing it is not
part of the formalization target. -/
theorem decoderProgram_operations_le_q_pow
    {n q d A K B W C k : ℕ}
    (hq : Nat.Prime q) (hd : 0 < d) (hdK : d < K)
    (hKn : K < n) (hnq : n ≤ q) (hB : 0 < B) (hkK : k ≤ K)
    (hmA : 0 < d ^ 3 * A) (hmAq : d ^ 3 * A ≤ q ^ 2)
    (hBq : B < q) (hW : W ≤ 2 * d ^ 4)
    (hdim :
      n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) (d ^ 3) W) <
        Module.finrank (ZMod q)
          (interpolationSpace q d (d ^ 3) A K B W C))
    (alpha : Fin n → ZMod q) (y : Fin n → ZMod q) :
    (decoderProgram hq hd hdK hB hkK hmA hmAq hBq hdim alpha y).operations ≤
      q ^ ((kopparty_theorem_4_3_algorithm.exponentConstant + 34) * (d + 1)) := by
  have hdq : d < q := hdK.trans_le (hKn.le.trans hnq)
  have hmatrix := interpolationMatrixOperationsFull_le_q_pow
    (K := K) (C := C) hq hd hdq hnq hBq hmAq hW
  have hgaussian := interpolationGaussianOperations_le_q_pow
    (K := K) (C := C) hq hd hdq hnq hBq hmAq hW
  have hfilter := candidateFilterOperations_le_q_pow hq hKn hnq
  have hsource := decoderProgram_operations_le
    hq hd hdK hKn hnq hB hkK hmA hmAq hBq hdim alpha y
  let c := kopparty_theorem_4_3_algorithm.exponentConstant
  let E := (c + 32) * (d + 1)
  have hc : 0 < c := kopparty_theorem_4_3_algorithm.exponentConstant_pos
  have hinterpolation :
      (interpolationMatrixOperationsFull n d (d ^ 3) A K B W C +
        (8 * (n * Nat.card (ContactEnvelopeCoordinate d (d ^ 3) W)) *
            Nat.card (InterpolationColumn d (d ^ 3) A K B W C) ^ 2 +
          Nat.card (InterpolationColumn d (d ^ 3) A K B W C))) ≤
        q ^ E := by
    have hm' : interpolationMatrixOperationsFull n d (d ^ 3) A K B W C ≤
        q ^ (12 * d + 25) :=
      hmatrix.trans (Nat.pow_le_pow_right hq.pos (by omega))
    have hg' :
        8 * (n * Nat.card (ContactEnvelopeCoordinate d (d ^ 3) W)) *
              Nat.card (InterpolationColumn d (d ^ 3) A K B W C) ^ 2 +
            Nat.card (InterpolationColumn d (d ^ 3) A K B W C) ≤
          q ^ (12 * d + 25) :=
      hgaussian.trans (Nat.pow_le_pow_right hq.pos (by omega))
    calc
      _ ≤ q ^ (12 * d + 25) + q ^ (12 * d + 25) :=
        Nat.add_le_add hm' hg'
      _ = 2 * q ^ (12 * d + 25) := by ring
      _ ≤ q * q ^ (12 * d + 25) :=
        Nat.mul_le_mul_right _ hq.two_le
      _ = q ^ (12 * d + 26) := by rw [← pow_succ']
      _ ≤ q ^ E := by
        apply Nat.pow_le_pow_right hq.pos
        change 12 * d + 26 ≤ (c + 32) * (d + 1)
        calc
          12 * d + 26 ≤ 32 * (d + 1) := by omega
          _ ≤ (c + 32) * (d + 1) :=
            Nat.mul_le_mul_right _ (by omega)
  have hroot :
      q ^ (c * (d + 1)) ≤ q ^ E :=
    Nat.pow_le_pow_right hq.pos
      (Nat.mul_le_mul_right _ (by omega))
  have hfiltered :
      q ^ (2 * d + 4) * candidateFilterOperations n K ≤ q ^ E := by
    calc
      q ^ (2 * d + 4) * candidateFilterOperations n K ≤
          q ^ (2 * d + 4) * q ^ 4 := Nat.mul_le_mul_left _ hfilter
      _ = q ^ (2 * d + 8) := by rw [← pow_add]
      _ ≤ q ^ E := by
        apply Nat.pow_le_pow_right hq.pos
        change 2 * d + 8 ≤ (c + 32) * (d + 1)
        calc
          2 * d + 8 ≤ 32 * (d + 1) := by omega
          _ ≤ (c + 32) * (d + 1) :=
            Nat.mul_le_mul_right _ (by omega)
  calc
    (decoderProgram hq hd hdK hB hkK hmA hmAq hBq hdim alpha y).operations ≤
        (interpolationMatrixOperationsFull n d (d ^ 3) A K B W C +
          (8 * (n * Nat.card (ContactEnvelopeCoordinate d (d ^ 3) W)) *
              Nat.card (InterpolationColumn d (d ^ 3) A K B W C) ^ 2 +
            Nat.card (InterpolationColumn d (d ^ 3) A K B W C))) +
          q ^ (c * (d + 1)) +
          q ^ (2 * d + 4) * candidateFilterOperations n K := by
      simpa [c] using hsource
    _ ≤ q ^ E + q ^ E + q ^ E := by
      gcongr
    _ = 3 * q ^ E := by ring
    _ ≤ q ^ 2 * q ^ E := by
      have : 3 ≤ q ^ 2 := by nlinarith [hq.two_le]
      exact Nat.mul_le_mul_right (q ^ E) this
    _ = q ^ (E + 2) := by
      rw [Nat.add_comm, pow_add]
    _ ≤ q ^ ((c + 34) * (d + 1)) :=
      Nat.pow_le_pow_right hq.pos (by
        calc
          E + 2 ≤ E + 2 * (d + 1) := by omega
          _ = (c + 34) * (d + 1) := by
            dsimp [E]
            ring)

end RSListDecoding
