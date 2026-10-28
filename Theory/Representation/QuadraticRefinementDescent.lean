module
public import Theory.Representation.ExtendScalars
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Basis.VectorSpace
/-!
# Descending invariant quadratic refinements

For any field extension, choose a base-field linear retraction of its scalar
embedding. Restrict an extension-field quadratic form to the original vectors
and compose its values with this retraction. Invariance is retained, and a
polar form already defined over the base field is recovered exactly.

This is the scalar-descent step in the degree-four binary SL₂ branch of
Aschbacher--Smith G.4.1, printed p.342. It needs no finite-field or uniqueness
assumption.
-/

public section
open scoped TensorProduct
namespace Representation.QuadraticRefinement
variable {F L G V : Type*} [Field F] [Field L] [Algebra F L] [Group G]
  [AddCommGroup V] [Module F V]

theorem exists_of_extendScalars (ρ : Representation F G V)
    (B : LinearMap.BilinForm F V)
    (Q : QuadraticForm L (L ⊗[F] V))
    (hQ : ∀ g v, Q (extendScalars L ρ g v) = Q v)
    (hpolar : Q.polarBilin = B.baseChange L) :
    ∃ R : QuadraticForm F V, R.polarBilin = B ∧ ∀ g v, R (ρ g v) = R v := by
  let i : F →ₗ[F] L := Algebra.linearMap F L
  let r := i.leftInverse
  have hr (x : F) : r (algebraMap F L x) = x :=
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (algebraMap F L).injective) x
  let j : V →ₗ[F] L ⊗[F] V := TensorProduct.mk F L V 1
  let R : QuadraticForm F V := r.compQuadraticMap ((Q.restrictScalars (S := F)).comp j)
  refine ⟨R, ?_, ?_⟩
  · ext v w
    change r (Q (1 ⊗ₜ[F] (v+w))) - r (Q (1 ⊗ₜ[F] v)) - r (Q (1 ⊗ₜ[F] w)) = B v w
    rw [← r.map_sub, ← r.map_sub, TensorProduct.tmul_add]
    change r (Q.polarBilin (1 ⊗ₜ[F] v) (1 ⊗ₜ[F] w)) = B v w
    rw [hpolar, LinearMap.BilinForm.baseChange_tmul]
    simpa only [one_mul, Algebra.smul_def, mul_one] using hr (B v w)
  · intro g v
    change r (Q (1 ⊗ₜ[F] ρ g v)) = r (Q (1 ⊗ₜ[F] v))
    have h := hQ g (1 ⊗ₜ[F] v)
    simpa only [extendScalars_apply, LinearMap.baseChange_tmul] using congrArg r h
end Representation.QuadraticRefinement
