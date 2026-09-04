import RSListDecoding.Defs.InterpolationSpace
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Dimension of the global interpolation space

The support-first definition of `interpolationSpace` comes with a canonical
monomial basis.  This file first identifies its rank with the number of
eligible exponent vectors.  It gives both the original rectangular lower
bound and a sharper simplex bound.  Splitting the `X` exponent into a residue
modulo `K - 1` and a block coordinate, then sharing the remaining slack among
that block coordinate and the `Y₀,Y₁` exponents, produces the exact factor
`(K - 1) * choose (J+2) 3`.

All rounding loss remains exposed in natural-number slack hypotheses.
-/

noncomputable section

namespace RSListDecoding

/-- Three-dimensional discrete simplex of total slack below `J`. -/
abbrev GlobalSlackSimplex (J : ℕ) :=
  Σ z : Fin J, ↥(Finset.Nat.antidiagonalTuple 3 z.val)

theorem card_antidiagonalTuple_three (z : ℕ) :
    (Finset.Nat.antidiagonalTuple 3 z).card = (z + 2).choose 2 := by
  induction z with
  | zero => simp [Finset.Nat.antidiagonalTuple_zero_right]
  | succ z ih =>
      change (List.Nat.antidiagonalTuple 3 (z + 1)).length =
        (z + 1 + 2).choose 2
      rw [List.Nat.antidiagonalTuple, List.Nat.antidiagonal_succ]
      simp only [List.flatMap_cons, List.length_append, List.length_map]
      simp_rw [List.Nat.antidiagonalTuple_two, List.length_map,
        List.Nat.length_antidiagonal]
      rw [Nat.choose_succ_succ]
      rw [List.length_flatMap]
      simp only [List.map_map, List.length_map]
      change (List.Nat.antidiagonalTuple 3 z).length =
        (z + 2).choose 2 at ih
      rw [List.Nat.antidiagonalTuple.eq_def, List.length_flatMap] at ih
      simp_rw [List.Nat.antidiagonalTuple_two, List.length_map,
        List.Nat.length_antidiagonal] at ih
      simp only [List.Nat.length_antidiagonal]
      have hmap :
          List.map ((fun a : ℕ × ℕ => a.2 + 1) ∘ Prod.map Nat.succ id)
              (List.Nat.antidiagonal z) =
            List.map (fun a : ℕ × ℕ => a.2 + 1)
              (List.Nat.antidiagonal z) := by
        apply List.map_congr_left
        intro a ha
        rcases a with ⟨a, b⟩
        rfl
      rw [hmap]
      rw [ih]
      simp

theorem card_globalSlackSimplex (J : ℕ) :
    Fintype.card (GlobalSlackSimplex J) = (J + 2).choose 3 := by
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_coe, card_antidiagonalTuple_three]
  rw [Fin.sum_univ_eq_sum_range (fun z => (z + 2).choose 2)]
  cases J with
  | zero => simp
  | succ J => simpa using Nat.sum_range_add_choose J 2

/-- The tuple carried by a simplex point determines the point itself. -/
theorem globalSlackSimplex_tuple_injective (J : ℕ) :
    Function.Injective (fun a : GlobalSlackSimplex J => a.2.1) := by
  rintro ⟨z, a⟩ ⟨z', a'⟩ haa'
  change a.1 = a'.1 at haa'
  have hsum := Finset.Nat.mem_antidiagonalTuple.mp a.2
  have hsum' := Finset.Nat.mem_antidiagonalTuple.mp a'.2
  have hzz' : z = z' := by
    apply Fin.ext
    rw [← hsum, ← hsum', haa']
  subst z'
  have ha : a = a' := Subtype.ext haa'
  subst a'
  rfl

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
  · rw [firstJetExponent_globalRectangleExponent]
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

/-- Simplex version of the global eligibility lemma.  Only the total slack
`s+b₀+b₁` is bounded, so one spends `J` once instead of bounding the three
coordinates independently. -/
theorem globalSimplexExponent_eligible {d m A K B W C J : ℕ}
    (hd : 1 ≤ d) (hJ : J ≤ m) (hdegree : C + J ≤ B)
    (hweighted : (K - 1) * (C + J) ≤ m * A)
    (c : ↥(goodHigherExponents d W C)) (r : Fin (K - 1))
    (a : GlobalSlackSimplex J) :
    GlobalEligibleExponent d m A K B W C
      (globalRectangleExponent hd K c.1 r
        (a.2.1 0) (a.2.1 1) (a.2.1 2)) := by
  have hc := mem_goodHigherExponents.mp c.2
  have hcWeight : higherJetWeight c.1 ≤ W := hc.1
  have hcDegree : higherJetDegree c.1 ≤ C := hc.2
  have hsum := Finset.Nat.mem_antidiagonalTuple.mp a.2.2
  rw [Fin.sum_univ_three] at hsum
  have hslack : a.2.1 0 + a.2.1 1 + a.2.1 2 < J := by
    rw [hsum]
    exact a.1.isLt
  have hslt : a.2.1 0 < m := lt_of_lt_of_le (by omega) hJ
  have htotal_lt :
      a.2.1 1 + a.2.1 2 + higherJetDegree c.1 < C + J := by
    omega
  have hblock_lt :
      a.2.1 0 + a.2.1 1 + a.2.1 2 + higherJetDegree c.1 <
        C + J := by
    omega
  have hweighted_lt :
      r.val + (K - 1) *
          (a.2.1 0 + a.2.1 1 + a.2.1 2 + higherJetDegree c.1) <
        (K - 1) * (C + J) := by
    calc
      r.val + (K - 1) *
          (a.2.1 0 + a.2.1 1 + a.2.1 2 + higherJetDegree c.1) <
          (K - 1) + (K - 1) *
            (a.2.1 0 + a.2.1 1 + a.2.1 2 +
              higherJetDegree c.1) := Nat.add_lt_add_right r.isLt _
      _ = (K - 1) *
          (a.2.1 0 + a.2.1 1 + a.2.1 2 +
            higherJetDegree c.1 + 1) := by ring
      _ ≤ (K - 1) * (C + J) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hblock_lt)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [firstJetExponent_globalRectangleExponent]
    omega
  · simpa using (Nat.le_trans (Nat.le_of_lt htotal_lt) hdegree)
  · simp only [globalRectangleExponent_x,
      totalJetDegree_globalRectangleExponent]
    calc
      r.val + (K - 1) * a.2.1 0 +
          (K - 1) *
            (a.2.1 1 + a.2.1 2 + higherJetDegree c.1) =
          r.val + (K - 1) *
            (a.2.1 0 + a.2.1 1 + a.2.1 2 +
              higherJetDegree c.1) := by ring
      _ < (K - 1) * (C + J) := hweighted_lt
      _ ≤ m * A := hweighted
  · simpa using hcWeight
  · simpa using hcDegree

/-- Pointwise simplex eligibility.  Unlike `globalSimplexExponent_eligible`,
the slack width may depend on the actual higher-jet exponent `c`; consequently
the degree and weighted-degree hypotheses spend `higherJetDegree c`, rather
than the ambient worst-case cap `C`. -/
theorem globalAdaptiveSimplexExponent_eligible
    {d m A K B W C : ℕ} {J : HigherJetExponent d → ℕ}
    (hd : 1 ≤ d)
    (hJ : ∀ c : ↥(goodHigherExponents d W C), J c.1 ≤ m)
    (hdegree : ∀ c : ↥(goodHigherExponents d W C),
      higherJetDegree c.1 + J c.1 ≤ B)
    (hweighted : ∀ c : ↥(goodHigherExponents d W C),
      (K - 1) * (higherJetDegree c.1 + J c.1) ≤ m * A)
    (c : ↥(goodHigherExponents d W C)) (r : Fin (K - 1))
    (a : GlobalSlackSimplex (J c.1)) :
    GlobalEligibleExponent d m A K B W C
      (globalRectangleExponent hd K c.1 r
        (a.2.1 0) (a.2.1 1) (a.2.1 2)) := by
  have hc := mem_goodHigherExponents.mp c.2
  have hsum := Finset.Nat.mem_antidiagonalTuple.mp a.2.2
  rw [Fin.sum_univ_three] at hsum
  have hslack : a.2.1 0 + a.2.1 1 + a.2.1 2 < J c.1 := by
    rw [hsum]
    exact a.1.isLt
  have hJc : J c.1 ≤ m := hJ c
  have hslt : a.2.1 0 < m := lt_of_lt_of_le (by omega) (hJ c)
  have htotal_lt :
      a.2.1 1 + a.2.1 2 + higherJetDegree c.1 <
        higherJetDegree c.1 + J c.1 := by omega
  have hblock_lt :
      a.2.1 0 + a.2.1 1 + a.2.1 2 + higherJetDegree c.1 <
        higherJetDegree c.1 + J c.1 := by omega
  have hweighted_lt :
      r.val + (K - 1) *
          (a.2.1 0 + a.2.1 1 + a.2.1 2 + higherJetDegree c.1) <
        (K - 1) * (higherJetDegree c.1 + J c.1) := by
    calc
      r.val + (K - 1) *
          (a.2.1 0 + a.2.1 1 + a.2.1 2 + higherJetDegree c.1) <
          (K - 1) + (K - 1) *
            (a.2.1 0 + a.2.1 1 + a.2.1 2 +
              higherJetDegree c.1) := Nat.add_lt_add_right r.isLt _
      _ = (K - 1) *
          (a.2.1 0 + a.2.1 1 + a.2.1 2 +
            higherJetDegree c.1 + 1) := by ring
      _ ≤ (K - 1) * (higherJetDegree c.1 + J c.1) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hblock_lt)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [firstJetExponent_globalRectangleExponent]
    omega
  · simpa using (Nat.le_trans (Nat.le_of_lt htotal_lt) (hdegree c))
  · simp only [globalRectangleExponent_x,
      totalJetDegree_globalRectangleExponent]
    calc
      r.val + (K - 1) * a.2.1 0 +
          (K - 1) *
            (a.2.1 1 + a.2.1 2 + higherJetDegree c.1) =
          r.val + (K - 1) *
            (a.2.1 0 + a.2.1 1 + a.2.1 2 +
              higherJetDegree c.1) := by ring
      _ < (K - 1) * (higherJetDegree c.1 + J c.1) := hweighted_lt
      _ ≤ m * A := hweighted c
  · simpa using hc.1
  · simpa using hc.2

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

/-- The simplex index family used by the sharper lower bound. -/
abbrev GlobalSimplexIndex (d W C K J : ℕ) :=
  ↥(goodHigherExponents d W C) × Fin (K - 1) × GlobalSlackSimplex J

/-- Degree-adaptive simplex family.  Each higher-jet monomial gets its own
slack width. -/
abbrev GlobalAdaptiveSimplexIndex (d W C K : ℕ)
    (J : HigherJetExponent d → ℕ) :=
  Σ c : ↥(goodHigherExponents d W C),
    Fin (K - 1) × GlobalSlackSimplex (J c.1)

/-- A canonical pointwise slack width, obtained by taking the minimum of the
first-jet, ordinary-degree, and weighted-degree residual budgets. -/
def adaptiveGlobalSlack {d : ℕ} (m A K B : ℕ)
    (c : HigherJetExponent d) : ℕ :=
  min m (min (B - higherJetDegree c)
    (m * A / (K - 1) - higherJetDegree c))

theorem adaptiveGlobalSlack_le_m {d m A K B : ℕ}
    (c : HigherJetExponent d) : adaptiveGlobalSlack m A K B c ≤ m :=
  min_le_left _ _

theorem higherJetDegree_add_adaptiveGlobalSlack_le_degreeBudget
    {d m A K B : ℕ} {c : HigherJetExponent d}
    (hcB : higherJetDegree c ≤ B) :
    higherJetDegree c + adaptiveGlobalSlack m A K B c ≤ B := by
  have hle : adaptiveGlobalSlack m A K B c ≤ B - higherJetDegree c :=
    (min_le_right _ _).trans (min_le_left _ _)
  omega

theorem weighted_adaptiveGlobalSlack_le_budget
    {d m A K B : ℕ} (hK : 1 < K) {c : HigherJetExponent d}
    (hcA : (K - 1) * higherJetDegree c ≤ m * A) :
    (K - 1) * (higherJetDegree c + adaptiveGlobalSlack m A K B c) ≤
      m * A := by
  have hk : 0 < K - 1 := by omega
  have hcdiv : higherJetDegree c ≤ m * A / (K - 1) :=
    (Nat.le_div_iff_mul_le hk).2 (by simpa [mul_comm] using hcA)
  have hle : adaptiveGlobalSlack m A K B c ≤
      m * A / (K - 1) - higherJetDegree c :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hadd : higherJetDegree c + adaptiveGlobalSlack m A K B c ≤
      m * A / (K - 1) := by omega
  exact (Nat.mul_le_mul_left (K - 1) hadd).trans (Nat.mul_div_le _ _)

/-- Every admissible uniform simplex is contained in the canonical adaptive
family. -/
theorem uniformSlack_le_adaptiveGlobalSlack
    {d m A K B W C J : ℕ} (hK : 1 < K)
    (hJ : J ≤ m) (hdegree : C + J ≤ B)
    (hweighted : (K - 1) * (C + J) ≤ m * A)
    (e : ↥(goodHigherExponents d W C)) :
    J ≤ adaptiveGlobalSlack m A K B e.1 := by
  have heC := (mem_goodHigherExponents.mp e.2).2
  have hk : 0 < K - 1 := by omega
  rw [adaptiveGlobalSlack, le_min_iff, le_min_iff]
  refine ⟨hJ, ?_, ?_⟩
  · omega
  · have hsum : (K - 1) * (higherJetDegree e.1 + J) ≤ m * A := by
      exact (Nat.mul_le_mul_left (K - 1) (Nat.add_le_add_right heC J)).trans
        hweighted
    have hdiv : higherJetDegree e.1 + J ≤ m * A / (K - 1) :=
      (Nat.le_div_iff_mul_le hk).2 (by simpa [mul_comm] using hsum)
    omega

theorem uniformGlobalSimplexCount_le_adaptive
    {d m A K B W C J : ℕ} (hK : 1 < K)
    (hJ : J ≤ m) (hdegree : C + J ≤ B)
    (hweighted : (K - 1) * (C + J) ≤ m * A) :
    (goodHigherExponents d W C).card * (K - 1) * (J + 2).choose 3 ≤
      (K - 1) * ∑ e : ↥(goodHigherExponents d W C),
        (adaptiveGlobalSlack m A K B e.1 + 2).choose 3 := by
  calc
    (goodHigherExponents d W C).card * (K - 1) * (J + 2).choose 3 =
        (K - 1) * ∑ _e : ↥(goodHigherExponents d W C),
          (J + 2).choose 3 := by
      simp [mul_comm, mul_left_comm]
    _ ≤ (K - 1) * ∑ e : ↥(goodHigherExponents d W C),
        (adaptiveGlobalSlack m A K B e.1 + 2).choose 3 := by
      gcongr with e
      exact uniformSlack_le_adaptiveGlobalSlack hK hJ hdegree hweighted e

/-- Map the simplex family into the eligible global monomials. -/
def globalSimplexEmbedding {d m A K B W C J : ℕ}
    (hd : 1 ≤ d) (hJ : J ≤ m) (hdegree : C + J ≤ B)
    (hweighted : (K - 1) * (C + J) ≤ m * A) :
    GlobalSimplexIndex d W C K J →
      ↥(globalEligibleExponents d m A K B W C)
  | ⟨c, r, a⟩ =>
      ⟨globalRectangleExponent hd K c.1 r
          (a.2.1 0) (a.2.1 1) (a.2.1 2),
        mem_globalEligibleExponents.mpr
          (globalSimplexExponent_eligible hd hJ hdegree hweighted c r a)⟩

/-- The simplex monomial map is injective. -/
theorem globalSimplexEmbedding_injective {d m A K B W C J : ℕ}
    (hd : 1 ≤ d) (hJ : J ≤ m) (hdegree : C + J ≤ B)
    (hweighted : (K - 1) * (C + J) ≤ m * A) :
    Function.Injective
      (globalSimplexEmbedding (W := W) hd hJ hdegree hweighted) := by
  rintro ⟨c, r, a⟩ ⟨c', r', a'⟩ heq
  have hexp :
      globalRectangleExponent hd K c.1 r
          (a.2.1 0) (a.2.1 1) (a.2.1 2) =
        globalRectangleExponent hd K c'.1 r'
          (a'.2.1 0) (a'.2.1 1) (a'.2.1 2) :=
    congrArg Subtype.val heq
  have hb₀ : a.2.1 1 = a'.2.1 1 := by
    simpa using DFunLike.congr_fun hexp (some (jetZeroIndex d))
  have hb₁ : a.2.1 2 = a'.2.1 2 := by
    simpa using DFunLike.congr_fun hexp (some (jetOneIndex d hd))
  have hc : c = c' := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    simpa using DFunLike.congr_fun hexp
      (some (higherJetIndexEmbedding d i))
  have hx : r.val + (K - 1) * a.2.1 0 =
      r'.val + (K - 1) * a'.2.1 0 := by
    simpa using DFunLike.congr_fun hexp none
  have hr : r = r' := by
    apply Fin.ext
    have hmod := congrArg (fun z : ℕ => z % (K - 1)) hx
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt,
      Nat.mod_eq_of_lt r'.isLt] using hmod
  have hs : a.2.1 0 = a'.2.1 0 := by
    have hk : 0 < K - 1 := Nat.zero_lt_of_lt r.isLt
    apply Nat.mul_left_cancel hk
    apply Nat.add_left_cancel (n := r.val)
    simpa [hr] using hx
  have haTuple : a.2.1 = a'.2.1 := by
    funext i
    fin_cases i
    · exact hs
    · exact hb₀
    · exact hb₁
  have ha : a = a' := globalSlackSimplex_tuple_injective J haTuple
  subst c'
  subst r'
  subst a'
  rfl

/-- Embed the degree-adaptive simplex family into the eligible monomials. -/
def globalAdaptiveSimplexEmbedding
    {d m A K B W C : ℕ} {J : HigherJetExponent d → ℕ}
    (hd : 1 ≤ d)
    (hJ : ∀ c : ↥(goodHigherExponents d W C), J c.1 ≤ m)
    (hdegree : ∀ c : ↥(goodHigherExponents d W C),
      higherJetDegree c.1 + J c.1 ≤ B)
    (hweighted : ∀ c : ↥(goodHigherExponents d W C),
      (K - 1) * (higherJetDegree c.1 + J c.1) ≤ m * A) :
    GlobalAdaptiveSimplexIndex d W C K J →
      ↥(globalEligibleExponents d m A K B W C)
  | ⟨c, r, a⟩ =>
      ⟨globalRectangleExponent hd K c.1 r
          (a.2.1 0) (a.2.1 1) (a.2.1 2),
        mem_globalEligibleExponents.mpr
          (globalAdaptiveSimplexExponent_eligible
            hd hJ hdegree hweighted c r a)⟩

theorem globalAdaptiveSimplexEmbedding_injective
    {d m A K B W C : ℕ} {J : HigherJetExponent d → ℕ}
    (hd : 1 ≤ d)
    (hJ : ∀ c : ↥(goodHigherExponents d W C), J c.1 ≤ m)
    (hdegree : ∀ c : ↥(goodHigherExponents d W C),
      higherJetDegree c.1 + J c.1 ≤ B)
    (hweighted : ∀ c : ↥(goodHigherExponents d W C),
      (K - 1) * (higherJetDegree c.1 + J c.1) ≤ m * A) :
    Function.Injective
      (globalAdaptiveSimplexEmbedding hd hJ hdegree hweighted) := by
  rintro ⟨c, r, a⟩ ⟨c', r', a'⟩ heq
  have hexp := congrArg Subtype.val heq
  change
    globalRectangleExponent hd K c.1 r
        (a.2.1 0) (a.2.1 1) (a.2.1 2) =
      globalRectangleExponent hd K c'.1 r'
        (a'.2.1 0) (a'.2.1 1) (a'.2.1 2) at hexp
  have hb₀ : a.2.1 1 = a'.2.1 1 := by
    simpa using DFunLike.congr_fun hexp (some (jetZeroIndex d))
  have hb₁ : a.2.1 2 = a'.2.1 2 := by
    simpa using DFunLike.congr_fun hexp (some (jetOneIndex d hd))
  have hc : c = c' := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    simpa using DFunLike.congr_fun hexp
      (some (higherJetIndexEmbedding d i))
  subst c'
  have hx : r.val + (K - 1) * a.2.1 0 =
      r'.val + (K - 1) * a'.2.1 0 := by
    simpa using DFunLike.congr_fun hexp none
  have hr : r = r' := by
    apply Fin.ext
    have hmod := congrArg (fun z : ℕ => z % (K - 1)) hx
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt,
      Nat.mod_eq_of_lt r'.isLt] using hmod
  have hs : a.2.1 0 = a'.2.1 0 := by
    have hk : 0 < K - 1 := Nat.zero_lt_of_lt r.isLt
    apply Nat.mul_left_cancel hk
    apply Nat.add_left_cancel (n := r.val)
    simpa [hr] using hx
  have haTuple : a.2.1 = a'.2.1 := by
    funext i
    fin_cases i
    · exact hs
    · exact hb₀
    · exact hb₁
  have ha : a = a' := globalSlackSimplex_tuple_injective (J c.1) haTuple
  subst r'
  subst a'
  rfl

/-- The rectangular index family has the advertised product cardinality. -/
theorem card_globalRectangleIndex (d W C K H : ℕ) :
    Fintype.card (GlobalRectangleIndex d W C K H) =
      (goodHigherExponents d W C).card * (K - 1) * H ^ 3 := by
  simp [GlobalRectangleIndex, pow_succ, mul_assoc]

theorem card_globalSimplexIndex (d W C K J : ℕ) :
    Fintype.card (GlobalSimplexIndex d W C K J) =
      (goodHigherExponents d W C).card * (K - 1) * (J + 2).choose 3 := by
  change Fintype.card
      (↥(goodHigherExponents d W C) × Fin (K - 1) ×
        GlobalSlackSimplex J) = _
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
  rw [card_globalSlackSimplex]
  ring

theorem card_globalAdaptiveSimplexIndex (d W C K : ℕ)
    (J : HigherJetExponent d → ℕ) :
    Fintype.card (GlobalAdaptiveSimplexIndex d W C K J) =
      (K - 1) * ∑ c : ↥(goodHigherExponents d W C),
        (J c.1 + 2).choose 3 := by
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_prod, Fintype.card_fin, card_globalSlackSimplex]
  rw [Finset.mul_sum]

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

/-- Simplex support-counting lower bound. -/
theorem card_globalEligibleExponents_simplex_lowerBound
    {d m A K B W C J : ℕ}
    (hd : 1 ≤ d) (hJ : J ≤ m) (hdegree : C + J ≤ B)
    (hweighted : (K - 1) * (C + J) ≤ m * A) :
    (goodHigherExponents d W C).card * (K - 1) * (J + 2).choose 3 ≤
      (globalEligibleExponents d m A K B W C).card := by
  rw [← card_globalSimplexIndex d W C K J, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective
    (globalSimplexEmbedding (W := W) hd hJ hdegree hweighted)
    (globalSimplexEmbedding_injective (W := W) hd hJ hdegree hweighted)

/-- Adaptive global support bound: no minimum slack is taken across the
higher-jet shell. -/
theorem card_globalEligibleExponents_adaptiveSimplex_lowerBound
    {d m A K B W C : ℕ} {J : HigherJetExponent d → ℕ}
    (hd : 1 ≤ d)
    (hJ : ∀ c : ↥(goodHigherExponents d W C), J c.1 ≤ m)
    (hdegree : ∀ c : ↥(goodHigherExponents d W C),
      higherJetDegree c.1 + J c.1 ≤ B)
    (hweighted : ∀ c : ↥(goodHigherExponents d W C),
      (K - 1) * (higherJetDegree c.1 + J c.1) ≤ m * A) :
    (K - 1) * ∑ c : ↥(goodHigherExponents d W C),
        (J c.1 + 2).choose 3 ≤
      (globalEligibleExponents d m A K B W C).card := by
  rw [← card_globalAdaptiveSimplexIndex d W C K J,
    ← Fintype.card_coe]
  exact Fintype.card_le_of_injective
    (globalAdaptiveSimplexEmbedding hd hJ hdegree hweighted)
    (globalAdaptiveSimplexEmbedding_injective hd hJ hdegree hweighted)

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

/-- Global dimension lower bound with the full three-dimensional simplex. -/
theorem finrank_interpolationSpace_simplex_lowerBound
    {q d m A K B W C J : ℕ} [Fact (1 < q)]
    (hd : 1 ≤ d) (hJ : J ≤ m) (hdegree : C + J ≤ B)
    (hweighted : (K - 1) * (C + J) ≤ m * A) :
    (goodHigherExponents d W C).card * (K - 1) * (J + 2).choose 3 ≤
      Module.finrank (ZMod q) (interpolationSpace q d m A K B W C) := by
  rw [finrank_interpolationSpace_eq_card]
  exact card_globalEligibleExponents_simplex_lowerBound hd hJ hdegree hweighted

/-- Rank form of the degree-adaptive global simplex sum. -/
theorem finrank_interpolationSpace_adaptiveSimplex_lowerBound
    {q d m A K B W C : ℕ} [Fact (1 < q)]
    {J : HigherJetExponent d → ℕ}
    (hd : 1 ≤ d)
    (hJ : ∀ c : ↥(goodHigherExponents d W C), J c.1 ≤ m)
    (hdegree : ∀ c : ↥(goodHigherExponents d W C),
      higherJetDegree c.1 + J c.1 ≤ B)
    (hweighted : ∀ c : ↥(goodHigherExponents d W C),
      (K - 1) * (higherJetDegree c.1 + J c.1) ≤ m * A) :
    (K - 1) * ∑ c : ↥(goodHigherExponents d W C),
        (J c.1 + 2).choose 3 ≤
      Module.finrank (ZMod q) (interpolationSpace q d m A K B W C) := by
  rw [finrank_interpolationSpace_eq_card]
  exact card_globalEligibleExponents_adaptiveSimplex_lowerBound
    hd hJ hdegree hweighted

end RSListDecoding
