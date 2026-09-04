import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi

/-!
# A common kernel for finitely many linear constraints

This file isolates the finite-dimensional linear algebra used by interpolation:
if the total dimension of a finite family of constraint spaces is smaller than
the source dimension, then all of the constraints have a common nonzero
solution.
-/

noncomputable section

namespace RSListDecoding

variable {F : Type*} [Field F]
variable {ι : Type*} [Fintype ι]
variable {V W : Type*}
variable [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- Aggregate a family of local constraint maps into their product map. -/
def aggregateLinearMap (φ : ι → V →ₗ[F] W) : V →ₗ[F] (ι → W) :=
  LinearMap.pi φ

omit [Fintype ι] [FiniteDimensional F V] [FiniteDimensional F W] in
@[simp]
theorem aggregateLinearMap_apply (φ : ι → V →ₗ[F] W) (v : V) (i : ι) :
    aggregateLinearMap φ v i = φ i v :=
  rfl

/-- The dimension of a finite product of copies of one constraint space. -/
theorem finrank_pi_const :
    Module.finrank F (ι → W) = Fintype.card ι * Module.finrank F W := by
  rw [Module.finrank_pi_fintype]
  simp

/-- If the sum of the local constraint dimensions is smaller than the source
dimension, the constraints have a common nonzero solution. -/
theorem exists_ne_zero_forall_apply_eq_zero
    (φ : ι → V →ₗ[F] W)
    (hφ : Fintype.card ι * Module.finrank F W < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, φ i v = 0 := by
  let Φ : V →ₗ[F] (ι → W) := aggregateLinearMap φ
  have hdim : Module.finrank F (ι → W) < Module.finrank F V := by
    simpa only [finrank_pi_const] using hφ
  have hker : LinearMap.ker Φ ≠ ⊥ := Φ.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨v, hvker, hvne⟩ := (Submodule.ne_bot_iff Φ.ker).mp hker
  refine ⟨v, hvne, fun i ↦ ?_⟩
  have hvzero : Φ v = 0 := LinearMap.mem_ker.mp hvker
  simpa only [Φ, aggregateLinearMap_apply, Pi.zero_apply] using congrFun hvzero i

end RSListDecoding
