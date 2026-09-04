import Mathlib.Data.Nat.Basic

/-!
# Finite-field operation costs

This file fixes the cost model used by the algorithmic list-decoding
extension.  A computation carries its mathematical result together with the
number of charged field operations.  The charged primitives are addition,
subtraction, negation, multiplication, inversion, and equality testing; each
costs one operation.  Pure control, indexing, natural-number arithmetic, and
allocation cost zero.

This is deliberately an algebraic-operation model.  In particular, nothing
in this file identifies one operation in `ZMod q` with one bit operation or
one machine instruction.
-/

namespace RSListDecoding

/-- A mathematical result paired with an exact finite-field operation count.

The type is intentionally transparent: cost theorems are proved from the
definitions of the algorithms which produce these values. -/
structure FieldCost (α : Type*) where
  result : α
  operations : ℕ
deriving Repr

namespace FieldCost

variable {α β F : Type*}

/-- Return a value without performing a field operation. -/
def pure (a : α) : FieldCost α := ⟨a, 0⟩

/-- Sequential composition adds the operation counts. -/
def bind (x : FieldCost α) (f : α → FieldCost β) : FieldCost β :=
  ⟨(f x.result).result, x.operations + (f x.result).operations⟩

/-- Apply a cost-free function to the result. -/
def map (f : α → β) (x : FieldCost α) : FieldCost β :=
  ⟨f x.result, x.operations⟩

/-- Charge a specified number of operations for an already described step. -/
def charge (n : ℕ) (a : α) : FieldCost α := ⟨a, n⟩

@[simp] theorem pure_result (a : α) : (pure a).result = a := rfl
@[simp] theorem pure_operations (a : α) : (pure a).operations = 0 := rfl
@[simp] theorem bind_result (x : FieldCost α) (f : α → FieldCost β) :
    (bind x f).result = (f x.result).result := rfl
@[simp] theorem bind_operations (x : FieldCost α) (f : α → FieldCost β) :
    (bind x f).operations = x.operations + (f x.result).operations := rfl
@[simp] theorem map_result (f : α → β) (x : FieldCost α) :
    (map f x).result = f x.result := rfl
@[simp] theorem map_operations (f : α → β) (x : FieldCost α) :
    (map f x).operations = x.operations := rfl
@[simp] theorem charge_result (n : ℕ) (a : α) : (charge n a).result = a := rfl
@[simp] theorem charge_operations (n : ℕ) (a : α) :
    (charge n a).operations = n := rfl

theorem bind_operations_le {x : FieldCost α} {f : α → FieldCost β}
    {a b : ℕ} (hx : x.operations ≤ a)
    (hf : (f x.result).operations ≤ b) :
    (bind x f).operations ≤ a + b := by
  simp only [bind_operations]
  exact Nat.add_le_add hx hf

/-- One charged field addition. -/
def add [Add F] (x y : F) : FieldCost F := charge 1 (x + y)

/-- One charged field subtraction. -/
def sub [Sub F] (x y : F) : FieldCost F := charge 1 (x - y)

/-- One charged field negation. -/
def neg [Neg F] (x : F) : FieldCost F := charge 1 (-x)

/-- One charged field multiplication. -/
def mul [Mul F] (x y : F) : FieldCost F := charge 1 (x * y)

/-- One charged field inversion.  Inversion of zero is permitted because the
Lean field convention makes it a total operation; algorithms must separately
prove that every pivot they invert is nonzero. -/
def inv [Inv F] (x : F) : FieldCost F := charge 1 x⁻¹

/-- One charged equality test. -/
def eq [DecidableEq F] (x y : F) : FieldCost Bool := charge 1 (x == y)

@[simp] theorem add_result [Add F] (x y : F) : (add x y).result = x + y := rfl
@[simp] theorem sub_result [Sub F] (x y : F) : (sub x y).result = x - y := rfl
@[simp] theorem neg_result [Neg F] (x : F) : (neg x).result = -x := rfl
@[simp] theorem mul_result [Mul F] (x y : F) : (mul x y).result = x * y := rfl
@[simp] theorem inv_result [Inv F] (x : F) : (inv x).result = x⁻¹ := rfl
@[simp] theorem eq_result [DecidableEq F] (x y : F) :
    (eq x y).result = (x == y) := rfl

@[simp] theorem add_operations [Add F] (x y : F) : (add x y).operations = 1 := rfl
@[simp] theorem sub_operations [Sub F] (x y : F) : (sub x y).operations = 1 := rfl
@[simp] theorem neg_operations [Neg F] (x : F) : (neg x).operations = 1 := rfl
@[simp] theorem mul_operations [Mul F] (x y : F) : (mul x y).operations = 1 := rfl
@[simp] theorem inv_operations [Inv F] (x : F) : (inv x).operations = 1 := rfl
@[simp] theorem eq_operations [DecidableEq F] (x y : F) : (eq x y).operations = 1 := rfl

end FieldCost

end RSListDecoding
