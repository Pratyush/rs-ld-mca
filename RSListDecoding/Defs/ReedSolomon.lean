import Mathlib.Data.ZMod.Basic

/-!
# Reed--Solomon messages and agreement lists

This file fixes the combinatorial objects used by the formalization target.
A message is represented by its `k` coefficients, so it denotes a polynomial
of degree strictly less than `k`.  The decoding list is the exact finite set of
messages meeting a prescribed integer agreement threshold.
-/

open scoped BigOperators

namespace RSListDecoding

/-- The coefficient vector of a polynomial of degree strictly less than `k`
over `ZMod q`. -/
abbrev Message (q k : ℕ) := Fin k → ZMod q

/-- Pad a degree-`< k` coefficient vector with zero coefficients to obtain a
degree-`< K` coefficient vector.  The inequality is part of the interface so
that this operation is used only as a genuine inclusion of message spaces. -/
def extendMessage {q k K : ℕ} (_hkK : k ≤ K) (p : Message q k) : Message q K :=
  fun i => if hi : (i : ℕ) < k then p ⟨i, hi⟩ else 0

/-- Restrict a degree-`< K` coefficient vector to its first `k`
coefficients. -/
def restrictMessage {q k K : ℕ} (hkK : k ≤ K)
    (p : Message q K) : Message q k :=
  fun i => p (Fin.castLE hkK i)

/-- Evaluate the polynomial represented by `p` at `x`. -/
def evaluateMessage {q k : ℕ} (p : Message q k) (x : ZMod q) : ZMod q :=
  ∑ i : Fin k, p i * x ^ (i : ℕ)

/-- The number of evaluation coordinates on which `p` agrees with `y`. -/
def agreementCount {n k q : ℕ} (α : Fin n → ZMod q) (y : Fin n → ZMod q)
    (p : Message q k) : ℕ :=
  (Finset.univ.filter fun i => evaluateMessage p (α i) = y i).card

/-- The exact list of degree-`< k` messages having at least `A` agreements.
The nonzero modulus witness supplies the finite instance for `ZMod q`. -/
def decodingList {n k q : ℕ} (hq : q ≠ 0)
    (α : Fin n → ZMod q) (y : Fin n → ZMod q)
    (A : ℕ) : Finset (Message q k) := by
  letI : NeZero q := ⟨hq⟩
  exact Finset.univ.filter fun p => A ≤ agreementCount α y p

/-- Every received word has at most `L` degree-`< k` messages with at least
`A` agreements on the evaluation set `α`. -/
def IsListDecodableAtAgreement {n k q : ℕ} (hq : q ≠ 0)
    (α : Fin n → ZMod q) (A L : ℕ) : Prop :=
  ∀ y : Fin n → ZMod q,
    (decodingList (k := k) hq α y A).card ≤ L

end RSListDecoding
