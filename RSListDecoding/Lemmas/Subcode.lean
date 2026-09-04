import RSListDecoding.Defs.ReedSolomon
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Reed--Solomon subcode monotonicity

A degree-`< k` coefficient vector embeds into the degree-`< K` message space
when `k ≤ K` by padding its high coefficients with zeros.  This file proves
that the embedding preserves evaluation and agreement exactly, and hence that
the smaller decoding list injects into the ambient decoding list.
-/

open scoped BigOperators

namespace RSListDecoding

/-- Zero extension uses the original coefficient at every index below `k`. -/
@[simp]
theorem extendMessage_apply_of_lt {q k K : ℕ} (hkK : k ≤ K)
    (p : Message q k) (i : Fin K) (hi : (i : ℕ) < k) :
    extendMessage hkK p i = p ⟨i, hi⟩ := by
  simp [extendMessage, hi]

/-- Every coefficient introduced above the original range is zero. -/
@[simp]
theorem extendMessage_apply_of_not_lt {q k K : ℕ} (hkK : k ≤ K)
    (p : Message q k) (i : Fin K) (hi : ¬(i : ℕ) < k) :
    extendMessage hkK p i = 0 := by
  simp [extendMessage, hi]

/-- Zero extension retains each coefficient in the original range. -/
@[simp]
theorem extendMessage_castLE {q k K : ℕ} (hkK : k ≤ K)
    (p : Message q k) (i : Fin k) :
    extendMessage hkK p (Fin.castLE hkK i) = p i := by
  simp [extendMessage]

/-- Zero extension is an injection of coefficient-vector message spaces. -/
theorem extendMessage_injective {q k K : ℕ} (hkK : k ≤ K) :
    Function.Injective (extendMessage (q := q) hkK) := by
  intro p r hpr
  funext i
  have hi := congrFun hpr (Fin.castLE hkK i)
  simpa using hi

@[simp]
theorem restrictMessage_extendMessage {q k K : ℕ} (hkK : k ≤ K)
    (p : Message q k) :
    restrictMessage hkK (extendMessage hkK p) = p := by
  funext i
  simp [restrictMessage]

/-- An ambient vector comes from the smaller message space exactly when
zero-extension of its restriction recovers it. -/
def ComesFromSubcode {q k K : ℕ} (hkK : k ≤ K)
    (p : Message q K) : Prop :=
  extendMessage hkK (restrictMessage hkK p) = p

theorem comesFromSubcode_extendMessage {q k K : ℕ} (hkK : k ≤ K)
    (p : Message q k) : ComesFromSubcode hkK (extendMessage hkK p) := by
  simp [ComesFromSubcode]

/-- Padding high coefficients with zeros does not change polynomial
evaluation. -/
theorem evaluateMessage_extendMessage {q k K : ℕ} (hkK : k ≤ K)
    (p : Message q k) (x : ZMod q) :
    evaluateMessage (extendMessage hkK p) x = evaluateMessage p x := by
  unfold evaluateMessage
  calc
    (∑ i : Fin K, extendMessage hkK p i * x ^ (i : ℕ)) =
        (∑ i : {i : Fin K // (i : ℕ) < k},
            extendMessage hkK p i * x ^ (i.1 : ℕ)) +
          ∑ i : {i : Fin K // ¬ (i : ℕ) < k},
            extendMessage hkK p i * x ^ (i.1 : ℕ) := by
              exact (Fintype.sum_subtype_add_sum_subtype
                (fun i : Fin K => (i : ℕ) < k)
                (fun i => extendMessage hkK p i * x ^ (i : ℕ))).symm
    _ = ∑ i : {i : Fin K // (i : ℕ) < k},
          extendMessage hkK p i * x ^ (i.1 : ℕ) := by
            have hzero : (∑ i : {i : Fin K // ¬ (i : ℕ) < k},
                extendMessage hkK p i * x ^ (i.1 : ℕ)) = 0 := by
              apply Fintype.sum_eq_zero
              intro i
              simp [extendMessage, i.property]
            rw [hzero, add_zero]
    _ = ∑ i : Fin k, p i * x ^ (i : ℕ) := by
      symm
      apply Fintype.sum_equiv (Fin.castLEquiv hkK)
      intro i
      simp [extendMessage]

/-- Zero extension preserves the number of agreement coordinates exactly. -/
theorem agreementCount_extendMessage {n q k K : ℕ} (hkK : k ≤ K)
    (α : Fin n → ZMod q) (y : Fin n → ZMod q) (p : Message q k) :
    agreementCount α y (extendMessage hkK p) = agreementCount α y p := by
  simp only [agreementCount, evaluateMessage_extendMessage]

/-- Characterize membership in the finite decoding list. -/
@[simp]
theorem mem_decodingList {n q k : ℕ} (hq : q ≠ 0)
    (α : Fin n → ZMod q) (y : Fin n → ZMod q) (A : ℕ)
    (p : Message q k) :
    p ∈ decodingList hq α y A ↔ A ≤ agreementCount α y p := by
  letI : NeZero q := ⟨hq⟩
  simp [decodingList]

/-- A message belongs to the ambient decoding list exactly when its original
coefficient vector belongs to the smaller decoding list. -/
theorem extendMessage_mem_decodingList_iff {n q k K : ℕ} (hq : q ≠ 0)
    (hkK : k ≤ K) (α : Fin n → ZMod q) (y : Fin n → ZMod q) (A : ℕ)
    (p : Message q k) :
    extendMessage hkK p ∈ decodingList hq α y A ↔
      p ∈ decodingList hq α y A := by
  rw [mem_decodingList, mem_decodingList, agreementCount_extendMessage]

/-- The list of degree-`< k` messages is no larger than the list of
degree-`< K` messages when `k ≤ K`. -/
theorem decodingList_card_le_of_le_dimension {n q k K : ℕ} (hq : q ≠ 0)
    (hkK : k ≤ K) (α : Fin n → ZMod q) (y : Fin n → ZMod q) (A : ℕ) :
    (decodingList (k := k) hq α y A).card ≤
      (decodingList (k := K) hq α y A).card := by
  let e : Message q k ↪ Message q K :=
    ⟨extendMessage hkK, extendMessage_injective hkK⟩
  have hsubset : (decodingList (k := k) hq α y A).map e ⊆
      decodingList (k := K) hq α y A := by
    intro P hP
    rw [Finset.mem_map] at hP
    obtain ⟨p, hp, rfl⟩ := hP
    exact (extendMessage_mem_decodingList_iff hq hkK α y A p).2 hp
  calc
    (decodingList (k := k) hq α y A).card =
        ((decodingList (k := k) hq α y A).map e).card :=
      (Finset.card_map e).symm
    _ ≤ (decodingList (k := K) hq α y A).card :=
      Finset.card_le_card hsubset

/-- Any list-size bound at dimension `K` also holds for every subcode of
dimension `k ≤ K`. -/
theorem isListDecodableAtAgreement_of_le_dimension {n q k K A L : ℕ}
    (hq : q ≠ 0) (hkK : k ≤ K) (α : Fin n → ZMod q)
    (hK : IsListDecodableAtAgreement (k := K) hq α A L) :
    IsListDecodableAtAgreement (k := k) hq α A L := by
  intro y
  exact (decodingList_card_le_of_le_dimension hq hkK α y A).trans (hK y)

end RSListDecoding
