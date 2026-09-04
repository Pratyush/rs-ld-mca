import RSListDecoding.Defs.InterpolationSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Dimension of the global interpolation space

The support-first definition of `interpolationSpace` comes with a canonical
monomial basis.  This file first identifies its rank with the number of
eligible exponent vectors.  It then gives a deliberately elementary lower
bound: for each good higher-jet exponent we place a rectangular family in
the four remaining directions.  Splitting the `X` exponent into a residue
modulo `K - 1` and a block coordinate produces the factor
`(K - 1) * H ^ 3`.

All rounding loss is exposed in the two natural-number slack hypotheses
`C + 2 * H ≤ B` and `(K - 1) * (C + 3 * H) ≤ m * A`.
-/

noncomputable section

namespace RSListDecoding

/-- The index of `Y₀` among the jet variables. -/
def jetZeroIndex (d : ℕ) : Fin (d + 1) := ⟨0, by omega⟩

/-- The index of `Y₁`.  The depth assumption is explicit because at depth
zero the differential-polynomial type has only the variable `Y₀`. -/
def jetOneIndex (d : ℕ) (hd : 1 ≤ d) : Fin (d + 1) := ⟨1, by omega⟩

/-- Embed the exponent coordinates for `Y₂, ..., Y_d` into the full tuple of
jet-variable exponents. -/
def higherJetIndexEmbedding (d : ℕ) : Fin (d - 1) ↪ Fin (d + 1) where
  toFun i := ⟨i.val + 2, by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    simpa using congrArg Fin.val hij

/-- The jet-variable part of one exponent in the rectangular family. -/
def rectangleJetExponent {d : ℕ} (hd : 1 ≤ d)
    (c : HigherJetExponent d) (b₀ b₁ : ℕ) : Fin (d + 1) →₀ ℕ :=
  Finsupp.single (jetZeroIndex d) b₀ +
    Finsupp.single (jetOneIndex d hd) b₁ +
    c.embDomain (higherJetIndexEmbedding d)

/-- One full exponent in the rectangular family.  Its `X` exponent is
`r + (K - 1) * s`, where `r` is the residue coordinate. -/
def globalRectangleExponent {d : ℕ} (hd : 1 ≤ d) (K : ℕ)
    (c : HigherJetExponent d) (r s b₀ b₁ : ℕ) : JetVariable d →₀ ℕ :=
  (rectangleJetExponent hd c b₀ b₁).optionElim (r + (K - 1) * s)

@[simp]
private theorem higherJetExponent_at_zero {d : ℕ}
    (c : HigherJetExponent d) :
    c.embDomain (higherJetIndexEmbedding d) (jetZeroIndex d) = 0 := by
  apply Finsupp.embDomain_notin_range
  rintro ⟨i, hi⟩
  have hval := congrArg Fin.val hi
  simp [higherJetIndexEmbedding, jetZeroIndex] at hval

@[simp]
private theorem higherJetExponent_at_one {d : ℕ} (hd : 1 ≤ d)
    (c : HigherJetExponent d) :
    c.embDomain (higherJetIndexEmbedding d) (jetOneIndex d hd) = 0 := by
  apply Finsupp.embDomain_notin_range
  rintro ⟨i, hi⟩
  have hval := congrArg Fin.val hi
  simp [higherJetIndexEmbedding, jetOneIndex] at hval

@[simp]
private theorem higherJetExponent_at_higher {d : ℕ}
    (c : HigherJetExponent d) (i : Fin (d - 1)) :
    c.embDomain (higherJetIndexEmbedding d) (higherJetIndexEmbedding d i) = c i :=
  Finsupp.embDomain_apply_self _ _ _

@[simp]
theorem globalRectangleExponent_x {d : ℕ} (hd : 1 ≤ d) (K : ℕ)
    (c : HigherJetExponent d) (r s b₀ b₁ : ℕ) :
    globalRectangleExponent hd K c r s b₀ b₁ none = r + (K - 1) * s := by
  simp [globalRectangleExponent]

@[simp]
theorem globalRectangleExponent_y0 {d : ℕ} (hd : 1 ≤ d) (K : ℕ)
    (c : HigherJetExponent d) (r s b₀ b₁ : ℕ) :
    globalRectangleExponent hd K c r s b₀ b₁ (some (jetZeroIndex d)) = b₀ := by
  have hne : jetZeroIndex d ≠ jetOneIndex d hd := by
    intro h
    have hval := congrArg Fin.val h
    simp [jetZeroIndex, jetOneIndex] at hval
  simp [globalRectangleExponent, rectangleJetExponent,
    higherJetExponent_at_zero, hne]

@[simp]
theorem globalRectangleExponent_y1 {d : ℕ} (hd : 1 ≤ d) (K : ℕ)
    (c : HigherJetExponent d) (r s b₀ b₁ : ℕ) :
    globalRectangleExponent hd K c r s b₀ b₁ (some (jetOneIndex d hd)) = b₁ := by
  have hne : jetOneIndex d hd ≠ jetZeroIndex d := by
    intro h
    have hval := congrArg Fin.val h
    simp [jetZeroIndex, jetOneIndex] at hval
  simp [globalRectangleExponent, rectangleJetExponent,
    higherJetExponent_at_one, hne]

@[simp]
theorem globalRectangleExponent_higher {d : ℕ} (hd : 1 ≤ d) (K : ℕ)
    (c : HigherJetExponent d) (r s b₀ b₁ : ℕ) (i : Fin (d - 1)) :
    globalRectangleExponent hd K c r s b₀ b₁
      (some (higherJetIndexEmbedding d i)) = c i := by
  have hne0 : higherJetIndexEmbedding d i ≠ jetZeroIndex d := by
    intro h
    have hval := congrArg Fin.val h
    simp [higherJetIndexEmbedding, jetZeroIndex] at hval
  have hne1 : higherJetIndexEmbedding d i ≠ jetOneIndex d hd := by
    intro h
    have hval := congrArg Fin.val h
    simp [higherJetIndexEmbedding, jetOneIndex] at hval
  simp [globalRectangleExponent, rectangleJetExponent,
    hne0, hne1]

/-- `embDomain` preserves the ordinary sum of a natural-valued exponent. -/
private theorem degree_embDomain_nat {α β : Type*} [Fintype α]
    (f : α ↪ β) (c : α →₀ ℕ) :
    Finsupp.degree (c.embDomain f) = Finsupp.degree c := by
  simp [Finsupp.degree_apply, Finsupp.support_embDomain]

/-- Reindexing a natural-valued exponent transports its weight function. -/
private theorem weight_embDomain_nat {α β : Type*} (w : β → ℕ)
    (f : α ↪ β) (c : α →₀ ℕ) :
    Finsupp.weight w (c.embDomain f) =
      Finsupp.weight (fun i => w (f i)) c := by
  simp [Finsupp.weight_apply, Finsupp.sum_embDomain]

@[simp]
theorem totalJetDegree_globalRectangleExponent {d : ℕ} (hd : 1 ≤ d)
    (K : ℕ) (c : HigherJetExponent d) (r s b₀ b₁ : ℕ) :
    totalJetDegree (globalRectangleExponent hd K c r s b₀ b₁) =
      b₀ + b₁ + higherJetDegree c := by
  simp [globalRectangleExponent, rectangleJetExponent, totalJetDegree,
    higherJetDegree, degree_embDomain_nat, add_assoc]

@[simp]
theorem firstJetExponent_globalRectangleExponent {d : ℕ} (hd : 1 ≤ d)
    (K : ℕ) (c : HigherJetExponent d) (r s b₀ b₁ : ℕ) :
    firstJetExponent (globalRectangleExponent hd K c r s b₀ b₁) = b₁ := by
  rw [firstJetExponent, globalRectangleExponent, Finsupp.some_optionElim]
  rw [rectangleJetExponent, map_add, map_add, Finsupp.weight_single,
    Finsupp.weight_single, weight_embDomain_nat]
  simp [jetZeroIndex, jetOneIndex, higherJetIndexEmbedding,
    Finsupp.weight_apply]

@[simp]
theorem fullHigherJetWeight_globalRectangleExponent {d : ℕ} (hd : 1 ≤ d)
    (K : ℕ) (c : HigherJetExponent d) (r s b₀ b₁ : ℕ) :
    fullHigherJetWeight (globalRectangleExponent hd K c r s b₀ b₁) =
      higherJetWeight c := by
  rw [fullHigherJetWeight, globalRectangleExponent, Finsupp.some_optionElim]
  rw [rectangleJetExponent, map_add, map_add, Finsupp.weight_single,
    Finsupp.weight_single, weight_embDomain_nat]
  simp [higherJetWeight, jetZeroIndex, jetOneIndex, higherJetIndexEmbedding]

@[simp]
theorem fullHigherJetDegree_globalRectangleExponent {d : ℕ} (hd : 1 ≤ d)
    (K : ℕ) (c : HigherJetExponent d) (r s b₀ b₁ : ℕ) :
    fullHigherJetDegree (globalRectangleExponent hd K c r s b₀ b₁) =
      higherJetDegree c := by
  rw [fullHigherJetDegree, globalRectangleExponent, Finsupp.some_optionElim]
  rw [rectangleJetExponent, map_add, map_add, Finsupp.weight_single,
    Finsupp.weight_single, weight_embDomain_nat]
  simp [higherJetDegree, Finsupp.degree_apply, jetZeroIndex, jetOneIndex,
    higherJetIndexEmbedding, Finsupp.weight_apply]
  rfl

/-- A rectangular exponent is globally eligible whenever its two explicit
slack inequalities fit inside the jet-degree and weighted-degree budgets. -/
theorem globalRectangleExponent_eligible {d m A K B W C H : ℕ}
    (hd : 1 ≤ d) (hH : H ≤ m) (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ m * A)
    (c : ↥(goodHigherExponents d W C))
    (r : Fin (K - 1)) (s b₀ b₁ : Fin H) :
    GlobalEligibleExponent d m A K B W C
      (globalRectangleExponent hd K c.1 r s b₀ b₁) := by
  have hc := (mem_goodHigherExponents.mp c.2)
  have hcWeight : higherJetWeight c.1 ≤ W := hc.1
  have hcDegree : higherJetDegree c.1 ≤ C := hc.2
  have htotal_lt :
      b₀.val + b₁.val + higherJetDegree c.1 < C + 2 * H := by
    omega
  have hblock_lt :
      s.val + b₀.val + b₁.val + higherJetDegree c.1 < C + 3 * H := by
    omega
  have hweighted_lt :
      r.val + (K - 1) *
          (s.val + b₀.val + b₁.val + higherJetDegree c.1) <
        (K - 1) * (C + 3 * H) := by
    calc
      r.val + (K - 1) *
          (s.val + b₀.val + b₁.val + higherJetDegree c.1) <
          (K - 1) + (K - 1) *
            (s.val + b₀.val + b₁.val + higherJetDegree c.1) :=
        Nat.add_lt_add_right r.isLt _
      _ = (K - 1) *
          (s.val + b₀.val + b₁.val + higherJetDegree c.1 + 1) := by ring
      _ ≤ (K - 1) * (C + 3 * H) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hblock_lt)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp
    omega
  · simpa using (Nat.le_trans (Nat.le_of_lt htotal_lt) hdegree)
  · simp only [globalRectangleExponent_x,
      totalJetDegree_globalRectangleExponent]
    calc
      r.val + (K - 1) * s.val +
          (K - 1) *
            (b₀.val + b₁.val + higherJetDegree c.1) =
          r.val + (K - 1) *
            (s.val + b₀.val + b₁.val + higherJetDegree c.1) := by ring
      _ < (K - 1) * (C + 3 * H) := hweighted_lt
      _ ≤ m * A := hweighted
  · simpa using hcWeight
  · simpa using hcDegree

/-- The finite rectangular index family used in the lower bound. -/
abbrev GlobalRectangleIndex (d W C K H : ℕ) :=
  ↥(goodHigherExponents d W C) ×
    Fin (K - 1) × Fin H × Fin H × Fin H

/-- Map the rectangular family into the subtype of eligible exponents. -/
def globalRectangleEmbedding {d m A K B W C H : ℕ}
    (hd : 1 ≤ d) (hH : H ≤ m) (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ m * A) :
    GlobalRectangleIndex d W C K H →
      ↥(globalEligibleExponents d m A K B W C)
  | ⟨c, r, s, b₀, b₁⟩ =>
      ⟨globalRectangleExponent hd K c.1 r s b₀ b₁,
        mem_globalEligibleExponents.mpr
          (globalRectangleExponent_eligible hd hH hdegree hweighted c r s b₀ b₁)⟩

/-- Distinct rectangular coordinates give distinct exponent vectors. -/
theorem globalRectangleEmbedding_injective {d m A K B W C H : ℕ}
    (hd : 1 ≤ d) (hH : H ≤ m) (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ m * A) :
    Function.Injective
      (globalRectangleEmbedding (W := W) hd hH hdegree hweighted) := by
  rintro ⟨c, r, s, b₀, b₁⟩ ⟨c', r', s', b₀', b₁'⟩ heq
  have hexp :
      globalRectangleExponent hd K c.1 r s b₀ b₁ =
        globalRectangleExponent hd K c'.1 r' s' b₀' b₁' :=
    congrArg Subtype.val heq
  have hb₀ : b₀ = b₀' := by
    apply Fin.ext
    simpa using DFunLike.congr_fun hexp (some (jetZeroIndex d))
  have hb₁ : b₁ = b₁' := by
    apply Fin.ext
    simpa using DFunLike.congr_fun hexp (some (jetOneIndex d hd))
  have hc : c = c' := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    simpa using DFunLike.congr_fun hexp
      (some (higherJetIndexEmbedding d i))
  have hx : r.val + (K - 1) * s.val =
      r'.val + (K - 1) * s'.val := by
    simpa using DFunLike.congr_fun hexp none
  have hr : r = r' := by
    apply Fin.ext
    have hmod := congrArg (fun z : ℕ => z % (K - 1)) hx
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt,
      Nat.mod_eq_of_lt r'.isLt] using hmod
  have hs : s = s' := by
    apply Fin.ext
    have hk : 0 < K - 1 := Nat.zero_lt_of_lt r.isLt
    apply Nat.mul_left_cancel hk
    apply Nat.add_left_cancel (n := r.val)
    simpa [hr] using hx
  subst c'
  subst r'
  subst s'
  subst b₀'
  subst b₁'
  rfl

/-- The rectangular index family has the advertised product cardinality. -/
theorem card_globalRectangleIndex (d W C K H : ℕ) :
    Fintype.card (GlobalRectangleIndex d W C K H) =
      (goodHigherExponents d W C).card * (K - 1) * H ^ 3 := by
  simp [GlobalRectangleIndex, pow_succ, mul_assoc]

/-- Pure support-counting form of the rectangular lower bound. -/
theorem card_globalEligibleExponents_lowerBound {d m A K B W C H : ℕ}
    (hd : 1 ≤ d) (hH : H ≤ m) (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ m * A) :
    (goodHigherExponents d W C).card * (K - 1) * H ^ 3 ≤
      (globalEligibleExponents d m A K B W C).card := by
  rw [← card_globalRectangleIndex d W C K H, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective
    (globalRectangleEmbedding (W := W) hd hH hdegree hweighted)
    (globalRectangleEmbedding_injective (W := W) hd hH hdegree hweighted)

/-- The canonical monomial basis identifies the rank of the interpolation
space with the exact number of eligible exponents. -/
theorem finrank_interpolationSpace_eq_card {q d m A K B W C : ℕ}
    [Fact (1 < q)] :
    Module.finrank (ZMod q) (interpolationSpace q d m A K B W C) =
      (globalEligibleExponents d m A K B W C).card := by
  let b : Module.Basis
      (↑(globalEligibleExponents d m A K B W C) :
        Set (JetVariable d →₀ ℕ))
      (ZMod q) (interpolationSpace q d m A K B W C) :=
    interpolationSpaceBasis q d m A K B W C
  rw [Module.finrank_eq_card_basis b]
  exact Fintype.card_coe _

/-- A generic, rounding-explicit lower bound on the global interpolation
dimension.  It is intentionally weaker than the manuscript's integral
estimate, but is fully discrete and supplies the same cubic dependence on
the chosen slack `H`. -/
theorem finrank_interpolationSpace_lowerBound {q d m A K B W C H : ℕ}
    [Fact (1 < q)] (hd : 1 ≤ d) (hH : H ≤ m)
    (hdegree : C + 2 * H ≤ B)
    (hweighted : (K - 1) * (C + 3 * H) ≤ m * A) :
    (goodHigherExponents d W C).card * (K - 1) * H ^ 3 ≤
      Module.finrank (ZMod q) (interpolationSpace q d m A K B W C) := by
  rw [finrank_interpolationSpace_eq_card]
  exact card_globalEligibleExponents_lowerBound hd hH hdegree hweighted

end RSListDecoding
