module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Coordinates for a tensor representation with trivial multiplicity action

A finite basis of the multiplicity space identifies a tensor product with
finitely many copies of the acted-on factor. Pure-tensor induction proves
that this identification preserves the action in every coordinate.

This is the linear-algebra bridge used for the natural section in
Aschbacher–Smith, Lemma 12.8.9(2–3), printed p.853.
-/

@[expose] public section
open scoped TensorProduct
namespace Representation
variable {k A M N W : Type*} [Field k] [Monoid A]
  [AddCommGroup M] [Module k M] [Module.Finite k M]
  [AddCommGroup N] [Module k N] [AddCommGroup W] [Module k W]

/-- Coordinates on the second factor, indexed by a finite basis of the first. -/
noncomputable def tensorFunctionCoordinates
    (j : M ⊗[k] N ≃ₗ[k] W) : W ≃ₗ[k] (Fin (Module.finrank k M) → N) :=
  j.symm.trans ((TensorProduct.equivFinsuppOfBasisLeft (Module.finBasis k M)).trans
    (Finsupp.linearEquivFunOnFinite k N _))

/-- Trivial action on the multiplicity factor gives coordinatewise equivariance. -/
theorem tensorFunctionCoordinates_equivariant
    (ρ : Representation k A N) (σ : Representation k A W)
    (j : M ⊗[k] N ≃ₗ[k] W)
    (hj : ∀ a z, j (Representation.tprod (Representation.trivial k A M) ρ a z) =
      σ a (j z)) (a : A) (w : W) (i : Fin (Module.finrank k M)) :
    tensorFunctionCoordinates j (σ a w) i = ρ a (tensorFunctionCoordinates j w i) := by
  obtain ⟨z, rfl⟩ := j.surjective w
  rw [← hj]
  simp only [tensorFunctionCoordinates, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m v =>
    simp [Representation.tprod_apply, Representation.trivial, TensorProduct.map_tmul]
  | add z t hz ht =>
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) hz ht
end Representation
