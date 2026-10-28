module
public import Mathlib.LinearAlgebra.Contraction

/-!
# Tensoring the invariant pairings in the Ree irreducibility argument

Tensor the actual linear equivalences to the two dual spaces, then use the
canonical dual-tensor equivalence. Evaluation on pure tensors is the product
of the factor pairings. Their invariance therefore tensors to invariance.
This is the pairing step used by the finite Ree annihilator argument,
Steinberg (1963), 12.2, with the source contravariant forms of §§2,4.
-/
public section
open scoped TensorProduct
namespace TensorProduct
variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F V] [FiniteDimensional F W]
noncomputable def pairingTensor (e : V ≃ₗ[F] Module.Dual F V)
    (f : W ≃ₗ[F] Module.Dual F W) : V ⊗[F] W ≃ₗ[F] Module.Dual F (V ⊗[F] W) :=
  (TensorProduct.congr e f).trans (TensorProduct.dualDistribEquiv F V W)

theorem pairingTensor_tmul (e : V ≃ₗ[F] Module.Dual F V)
    (f : W ≃ₗ[F] Module.Dual F W) (x y : V) (u v : W) :
    pairingTensor e f (x ⊗ₜ[F] u) (y ⊗ₜ[F] v) = e x y * f u v := by
  simp [pairingTensor, TensorProduct.dualDistribEquiv, TensorProduct.dualDistribEquivOfBasis]

theorem pairingTensor_invariant (e : V ≃ₗ[F] Module.Dual F V)
    (f : W ≃ₗ[F] Module.Dual F W) (A : Module.End F V) (B : Module.End F W)
    (he : ∀x y, e (A x) (A y) = e x y) (hf : ∀x y, f (B x) (B y) = f x y)
    (x y : V ⊗[F] W) : pairingTensor e f (TensorProduct.map A B x) (TensorProduct.map A B y) =
      pairingTensor e f x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | tmul c d => simp only [TensorProduct.map_tmul, pairingTensor_tmul, he, hf]
end TensorProduct
