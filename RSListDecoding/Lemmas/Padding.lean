import RSListDecoding.Defs.ReedSolomon

/-!
# Coordinate padding

A Reed--Solomon list bound on a larger evaluation set immediately implies
the same absolute-agreement bound on any puncturing.  Extending a received
word arbitrarily on the added coordinates therefore formalizes the standard
"pad, low-rate decode, and prune" reduction.
-/

namespace RSListDecoding

/-- Agreements on selected coordinates inject into agreements on an
extension of the evaluation set and received word. -/
theorem agreementCount_le_of_extension
    {n N k q : ℕ} (ι : Fin n ↪ Fin N)
    (α : Fin n → ZMod q) (αN : Fin N → ZMod q)
    (y : Fin n → ZMod q) (yN : Fin N → ZMod q)
    (hα : ∀ i, αN (ι i) = α i) (hy : ∀ i, yN (ι i) = y i)
    (p : Message q k) :
    agreementCount α y p ≤ agreementCount αN yN p := by
  let agreeing := Finset.univ.filter fun i : Fin n =>
    evaluateMessage p (α i) = y i
  let agreeingN := Finset.univ.filter fun i : Fin N =>
    evaluateMessage p (αN i) = yN i
  have hsubset : agreeing.map ι ≤ agreeingN := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, by simpa [hα, hy] using hi.2⟩
  change agreeing.card ≤ agreeingN.card
  rw [← Finset.card_map]
  exact Finset.card_le_card hsubset

/-- The decoding list on selected coordinates is contained in the list on
any extension with the same absolute agreement threshold. -/
theorem decodingList_card_le_of_extension
    {n N k q A : ℕ} (hq : q ≠ 0) (ι : Fin n ↪ Fin N)
    (α : Fin n → ZMod q) (αN : Fin N → ZMod q)
    (y : Fin n → ZMod q) (yN : Fin N → ZMod q)
    (hα : ∀ i, αN (ι i) = α i) (hy : ∀ i, yN (ι i) = y i) :
    (decodingList (k := k) hq α y A).card ≤
      (decodingList (k := k) hq αN yN A).card := by
  letI : NeZero q := ⟨hq⟩
  apply Finset.card_le_card
  intro p hp
  rw [decodingList, Finset.mem_filter] at hp ⊢
  exact ⟨Finset.mem_univ _, hp.2.trans (agreementCount_le_of_extension
    ι α αN y yN hα hy p)⟩

/-- Coordinate extension (padding) preserves every list-size bound at the
same absolute agreement threshold.  The values placed in the new received
coordinates are irrelevant because `Function.extend` may fill them
arbitrarily. -/
theorem isListDecodableAtAgreement_of_extension
    {n N k q A L : ℕ} (hq : q ≠ 0) (ι : Fin n ↪ Fin N)
    (α : Fin n → ZMod q) (αN : Fin N → ZMod q)
    (hα : ∀ i, αN (ι i) = α i)
    (hlarge : IsListDecodableAtAgreement (k := k) hq αN A L) :
    IsListDecodableAtAgreement (k := k) hq α A L := by
  intro y
  let yN : Fin N → ZMod q := Function.extend ι y 0
  have hy : ∀ i, yN (ι i) = y i := fun i => by
    exact ι.injective.extend_apply y 0 i
  exact (decodingList_card_le_of_extension hq ι α αN y yN hα hy).trans
    (hlarge yN)

end RSListDecoding
