import RSListDecoding.Lemmas.ContactEnvelopeCount
import RSListDecoding.Lemmas.GlobalDimension
import Mathlib.Algebra.Field.ZMod

/-!
# Comparing global interpolation dimension with local constraint dimension

This module contains the purely discrete cancellation step.  Analytic work is
isolated in two hypotheses: a shell ratio `N(W+d³) ≤ R|G|` and one final
natural-number inequality.  Everything else follows from the checked
monomial counts.
-/

noncomputable section

namespace RSListDecoding

/-- Fully adaptive dimension comparison.  The local side is the exact sum
over contact layers, and the global side is the exact sum of the simplex
volumes attached to individual higher-jet monomials.  Thus this theorem
performs no replacement by a worst layer or a minimum slack. -/
theorem total_coupledContactEnvelope_finrank_lt_interpolationSpace_adaptive
    {q d m A K B W C n : ℕ} [hq : Fact (Nat.Prime q)]
    {J : HigherJetExponent d → ℕ}
    (hd : 0 < d)
    (hJ : ∀ c : ↥(goodHigherExponents d W C), J c.1 ≤ m)
    (hdegree : ∀ c : ↥(goodHigherExponents d W C),
      higherJetDegree c.1 + J c.1 ≤ B)
    (hweighted : ∀ c : ↥(goodHigherExponents d W C),
      (K - 1) * (higherJetDegree c.1 + J c.1) ≤ m * A)
    (hsums :
      n * coupledContactEnvelopeCount d m W <
        (K - 1) * ∑ c : ↥(goodHigherExponents d W C),
          (J c.1 + 2).choose 3) :
    n * Module.finrank (ZMod q)
          (coupledContactEnvelopeSpace (R := ZMod q) (d := d) m W) <
      Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C) := by
  letI : Fact (1 < q) := ⟨hq.out.one_lt⟩
  have hlocal := finrank_coupledContactEnvelopeSpace_le
    (R := ZMod q) (d := d) (m := m) (W := W) hd
  have hglobal := finrank_interpolationSpace_adaptiveSimplex_lowerBound
    (q := q) (m := m) (A := A) (K := K) (B := B)
    (W := W) (C := C) hd hJ hdegree hweighted
  exact (Nat.mul_le_mul_left n hlocal).trans_lt (hsums.trans_le hglobal)

/-- Adaptive comparison using the strongest support-only local envelope. -/
theorem total_sharpenedContactEnvelope_finrank_lt_interpolationSpace_adaptive
    {q d m A K B W C n : ℕ} [hq : Fact (Nat.Prime q)]
    {J : HigherJetExponent d → ℕ}
    (hd : 0 < d)
    (hJ : ∀ c : ↥(goodHigherExponents d W C), J c.1 ≤ m)
    (hdegree : ∀ c : ↥(goodHigherExponents d W C),
      higherJetDegree c.1 + J c.1 ≤ B)
    (hweighted : ∀ c : ↥(goodHigherExponents d W C),
      (K - 1) * (higherJetDegree c.1 + J c.1) ≤ m * A)
    (hsums :
      n * sharpenedContactEnvelopeCount d m W <
        (K - 1) * ∑ c : ↥(goodHigherExponents d W C),
          (J c.1 + 2).choose 3) :
    n * Module.finrank (ZMod q)
          (sharpenedContactEnvelopeSpace (R := ZMod q) (d := d) m W) <
      Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C) := by
  letI : Fact (1 < q) := ⟨hq.out.one_lt⟩
  have hlocal := finrank_sharpenedContactEnvelopeSpace_le
    (R := ZMod q) (d := d) (m := m) (W := W) hd
  have hglobal := finrank_interpolationSpace_adaptiveSimplex_lowerBound
    (q := q) (m := m) (A := A) (K := K) (B := B)
    (W := W) (C := C) hd hJ hdegree hweighted
  exact (Nat.mul_le_mul_left n hlocal).trans_lt (hsums.trans_le hglobal)

/-- Multiplicity-generic version of the final simplex comparison.  Unlike the
specialized capstones below, this theorem does not assume `m = d^3`: it uses
the generic contact-envelope count

`m * (m / d + 1) * (2 * m) * N_d(W+m)`.

This is the finite combinatorial statement needed by alternative
multiplicity schedules, including the quadratic schedule. -/
theorem total_contactEnvelope_finrank_lt_interpolationSpace_simplex_general
    {q d m A K B W C J R n : ℕ} [hq : Fact (Nat.Prime q)]
    (hd : 0 < d)
    (hJ : J ≤ m) (hdegree : C + J ≤ B)
    (hweighted : (K - 1) * (C + J) ≤ m * A)
    (hshell : scaledExponentCount d (W + m) ≤
      R * goodScaledExponentCount d W C)
    (harithmetic :
      n * (m * (m / d + 1) * (2 * m) * R) <
        (K - 1) * (J + 2).choose 3) :
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
      Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C) := by
  letI : Fact (1 < q) := ⟨hq.out.one_lt⟩
  have hlocal :=
    finrank_contactEnvelopeSpace_le
      (R := ZMod q) (d := d) (m := m) (W := W) hd
  have hglobal := finrank_interpolationSpace_simplex_lowerBound
    (q := q) (m := m) (A := A) (K := K) (B := B)
    (W := W) (C := C) (J := J) hd hJ hdegree hweighted
  have hG : 0 < goodScaledExponentCount d W C :=
    goodScaledExponentCount_pos d W C
  calc
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W)
        ≤ n * (m * (m / d + 1) * (2 * m) *
          scaledExponentCount d (W + m)) := Nat.mul_le_mul_left n hlocal
    _ ≤ n * (m * (m / d + 1) * (2 * m) *
          (R * goodScaledExponentCount d W C)) := by gcongr
    _ = (n * (m * (m / d + 1) * (2 * m) * R)) *
          goodScaledExponentCount d W C := by ring
    _ < ((K - 1) * (J + 2).choose 3) *
          goodScaledExponentCount d W C :=
      Nat.mul_lt_mul_of_pos_right harithmetic hG
    _ = (goodHigherExponents d W C).card * (K - 1) *
          (J + 2).choose 3 := by
      rw [← goodScaledExponentCount_eq_card_goodHigherExponents]
      ring
    _ ≤ Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C) := hglobal

/-- Multiplicity-generic simplex comparison with the exact triangular local
contact count.  Whenever `d ∣ m`, the local factor is

`m * (m / d + 1) * m * N_d(W+m)`,

exactly half the former rectangular bound. -/
theorem total_contactEnvelope_finrank_lt_interpolationSpace_simplex_divisible
    {q d m A K B W C J R n : ℕ} [hq : Fact (Nat.Prime q)]
    (hd : 0 < d) (hdm : d ∣ m)
    (hJ : J ≤ m) (hdegree : C + J ≤ B)
    (hweighted : (K - 1) * (C + J) ≤ m * A)
    (hshell : scaledExponentCount d (W + m) ≤
      R * goodScaledExponentCount d W C)
    (harithmetic :
      n * (m * (m / d + 1) * m * R) <
        (K - 1) * (J + 2).choose 3) :
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W) <
      Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C) := by
  letI : Fact (1 < q) := ⟨hq.out.one_lt⟩
  have hlocal :=
    finrank_contactEnvelopeSpace_le_divisible
      (R := ZMod q) (d := d) (m := m) (W := W) hd hdm
  have hglobal := finrank_interpolationSpace_simplex_lowerBound
    (q := q) (m := m) (A := A) (K := K) (B := B)
    (W := W) (C := C) (J := J) hd hJ hdegree hweighted
  have hG : 0 < goodScaledExponentCount d W C :=
    goodScaledExponentCount_pos d W C
  calc
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) m W)
        ≤ n * (m * (m / d + 1) * m *
          scaledExponentCount d (W + m)) := Nat.mul_le_mul_left n hlocal
    _ ≤ n * (m * (m / d + 1) * m *
          (R * goodScaledExponentCount d W C)) := by gcongr
    _ = (n * (m * (m / d + 1) * m * R)) *
          goodScaledExponentCount d W C := by ring
    _ < ((K - 1) * (J + 2).choose 3) *
          goodScaledExponentCount d W C :=
      Nat.mul_lt_mul_of_pos_right harithmetic hG
    _ = (goodHigherExponents d W C).card * (K - 1) *
          (J + 2).choose 3 := by
      rw [← goodScaledExponentCount_eq_card_goodHigherExponents]
      ring
    _ ≤ Module.finrank (ZMod q)
          (interpolationSpace q d m A K B W C) := hglobal

theorem card_goodHigherExponents_pos (d W C : ℕ) :
    0 < (goodHigherExponents d W C).card := by
  rw [← goodScaledExponentCount_eq_card_goodHigherExponents]
  exact goodScaledExponentCount_pos d W C

/-- The direct contact-envelope count is smaller than the global
interpolation dimension once the shell estimate and the final scalar
inequality are supplied. -/
theorem total_contactEnvelope_finrank_lt_interpolationSpace
    {q d A K B W C H R n : ℕ} [hq : Fact (Nat.Prime q)]
    (hd : 0 < d)
    (hH : H ≤ d ^ 3) (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ d ^ 3 * A)
    (hshell : scaledExponentCount d (W + d ^ 3) ≤
      R * goodScaledExponentCount d W C)
    (harithmetic : n * (4 * d ^ 8 * R) < (K - 1) * H ^ 3) :
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) (d ^ 3) W) <
      Module.finrank (ZMod q)
          (interpolationSpace q d (d ^ 3) A K B W C) := by
  letI : Fact (1 < q) := ⟨hq.out.one_lt⟩
  have hlocal :=
    finrank_contactEnvelopeSpace_le_four_mul_d_pow_eight
      (R := ZMod q) (W := W) hd
  have hglobal := finrank_interpolationSpace_lowerBound
    (q := q) (m := d ^ 3) (A := A) (K := K) (B := B)
    (W := W) (C := C) (H := H) hd hH hdegree hweighted
  have hG : 0 < goodScaledExponentCount d W C :=
    goodScaledExponentCount_pos d W C
  calc
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) (d ^ 3) W)
        ≤ n * (4 * d ^ 8 * scaledExponentCount d (W + d ^ 3)) :=
      Nat.mul_le_mul_left n hlocal
    _ ≤ n * (4 * d ^ 8 * (R * goodScaledExponentCount d W C)) := by
      gcongr
    _ = (n * (4 * d ^ 8 * R)) * goodScaledExponentCount d W C := by ring
    _ < ((K - 1) * H ^ 3) * goodScaledExponentCount d W C :=
      Nat.mul_lt_mul_of_pos_right harithmetic hG
    _ = (goodHigherExponents d W C).card * (K - 1) * H ^ 3 := by
      rw [← goodScaledExponentCount_eq_card_goodHigherExponents]
      ring
    _ ≤ Module.finrank (ZMod q)
          (interpolationSpace q d (d ^ 3) A K B W C) := hglobal

/-- Sharpened comparison using the exact triangular contact geometry. -/
theorem total_contactEnvelope_finrank_lt_interpolationSpace_sharp
    {q d A K B W C H R n : ℕ} [hq : Fact (Nat.Prime q)]
    (hd : 0 < d)
    (hH : H ≤ d ^ 3) (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ d ^ 3 * A)
    (hshell : scaledExponentCount d (W + d ^ 3) ≤
      R * goodScaledExponentCount d W C)
    (harithmetic : n * (2 * d ^ 8 * R) < (K - 1) * H ^ 3) :
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) (d ^ 3) W) <
      Module.finrank (ZMod q)
          (interpolationSpace q d (d ^ 3) A K B W C) := by
  letI : Fact (1 < q) := ⟨hq.out.one_lt⟩
  have hlocal :=
    finrank_contactEnvelopeSpace_le_two_mul_d_pow_eight
      (R := ZMod q) (W := W) hd
  have hglobal := finrank_interpolationSpace_lowerBound
    (q := q) (m := d ^ 3) (A := A) (K := K) (B := B)
    (W := W) (C := C) (H := H) hd hH hdegree hweighted
  have hG : 0 < goodScaledExponentCount d W C :=
    goodScaledExponentCount_pos d W C
  calc
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) (d ^ 3) W)
        ≤ n * (2 * d ^ 8 * scaledExponentCount d (W + d ^ 3)) :=
      Nat.mul_le_mul_left n hlocal
    _ ≤ n * (2 * d ^ 8 * (R * goodScaledExponentCount d W C)) := by
      gcongr
    _ = (n * (2 * d ^ 8 * R)) * goodScaledExponentCount d W C := by ring
    _ < ((K - 1) * H ^ 3) * goodScaledExponentCount d W C :=
      Nat.mul_lt_mul_of_pos_right harithmetic hG
    _ = (goodHigherExponents d W C).card * (K - 1) * H ^ 3 := by
      rw [← goodScaledExponentCount_eq_card_goodHigherExponents]
      ring
    _ ≤ Module.finrank (ZMod q)
          (interpolationSpace q d (d ^ 3) A K B W C) := hglobal

/-- Exact triangular-contact comparison. -/
theorem total_contactEnvelope_finrank_lt_interpolationSpace_exact
    {q d A K B W C H R n : ℕ} [hq : Fact (Nat.Prime q)]
    (hd : 0 < d)
    (hH : H ≤ d ^ 3) (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ d ^ 3 * A)
    (hshell : scaledExponentCount d (W + d ^ 3) ≤
      R * goodScaledExponentCount d W C)
    (harithmetic :
      n * ((d ^ 8 + d ^ 6) * R) < (K - 1) * H ^ 3) :
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) (d ^ 3) W) <
      Module.finrank (ZMod q)
          (interpolationSpace q d (d ^ 3) A K B W C) := by
  letI : Fact (1 < q) := ⟨hq.out.one_lt⟩
  have hlocal :=
    finrank_contactEnvelopeSpace_le_exact
      (R := ZMod q) (W := W) hd
  have hglobal := finrank_interpolationSpace_lowerBound
    (q := q) (m := d ^ 3) (A := A) (K := K) (B := B)
    (W := W) (C := C) (H := H) hd hH hdegree hweighted
  have hG : 0 < goodScaledExponentCount d W C :=
    goodScaledExponentCount_pos d W C
  calc
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) (d ^ 3) W)
        ≤ n * ((d ^ 8 + d ^ 6) *
          scaledExponentCount d (W + d ^ 3)) := Nat.mul_le_mul_left n hlocal
    _ ≤ n * ((d ^ 8 + d ^ 6) *
          (R * goodScaledExponentCount d W C)) := by gcongr
    _ = (n * ((d ^ 8 + d ^ 6) * R)) *
          goodScaledExponentCount d W C := by ring
    _ < ((K - 1) * H ^ 3) * goodScaledExponentCount d W C :=
      Nat.mul_lt_mul_of_pos_right harithmetic hG
    _ = (goodHigherExponents d W C).card * (K - 1) * H ^ 3 := by
      rw [← goodScaledExponentCount_eq_card_goodHigherExponents]
      ring
    _ ≤ Module.finrank (ZMod q)
          (interpolationSpace q d (d ^ 3) A K B W C) := hglobal

/-- Final comparison using both exact triangular contacts and the exact
shared three-dimensional slack simplex. -/
theorem total_contactEnvelope_finrank_lt_interpolationSpace_simplex
    {q d A K B W C J R n : ℕ} [hq : Fact (Nat.Prime q)]
    (hd : 0 < d)
    (hJ : J ≤ d ^ 3) (hdegree : C + J ≤ B)
    (hweighted : (K - 1) * (C + J) ≤ d ^ 3 * A)
    (hshell : scaledExponentCount d (W + d ^ 3) ≤
      R * goodScaledExponentCount d W C)
    (harithmetic :
      n * ((d ^ 8 + d ^ 6) * R) <
        (K - 1) * (J + 2).choose 3) :
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) (d ^ 3) W) <
      Module.finrank (ZMod q)
          (interpolationSpace q d (d ^ 3) A K B W C) := by
  letI : Fact (1 < q) := ⟨hq.out.one_lt⟩
  have hlocal :=
    finrank_contactEnvelopeSpace_le_exact
      (R := ZMod q) (W := W) hd
  have hglobal := finrank_interpolationSpace_simplex_lowerBound
    (q := q) (m := d ^ 3) (A := A) (K := K) (B := B)
    (W := W) (C := C) (J := J) hd hJ hdegree hweighted
  have hG : 0 < goodScaledExponentCount d W C :=
    goodScaledExponentCount_pos d W C
  calc
    n * Module.finrank (ZMod q)
          (contactEnvelopeSpace (R := ZMod q) (d := d) (d ^ 3) W)
        ≤ n * ((d ^ 8 + d ^ 6) *
          scaledExponentCount d (W + d ^ 3)) := Nat.mul_le_mul_left n hlocal
    _ ≤ n * ((d ^ 8 + d ^ 6) *
          (R * goodScaledExponentCount d W C)) := by gcongr
    _ = (n * ((d ^ 8 + d ^ 6) * R)) *
          goodScaledExponentCount d W C := by ring
    _ < ((K - 1) * (J + 2).choose 3) *
          goodScaledExponentCount d W C :=
      Nat.mul_lt_mul_of_pos_right harithmetic hG
    _ = (goodHigherExponents d W C).card * (K - 1) *
          (J + 2).choose 3 := by
      rw [← goodScaledExponentCount_eq_card_goodHigherExponents]
      ring
    _ ≤ Module.finrank (ZMod q)
          (interpolationSpace q d (d ^ 3) A K B W C) := hglobal

end RSListDecoding
