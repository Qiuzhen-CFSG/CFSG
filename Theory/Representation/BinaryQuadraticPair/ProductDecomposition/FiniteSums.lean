module

public import Theory.Representation.InvertedCubicTensor
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Finite natural-module sums from the inverted cubic tensor equivalence

For a binary S₃ representation with zero cubic fixed space, choose a finite
basis of the transposition-fixed multiplicity space. The tensor equivalence
then becomes an equivariant linear equivalence from a finite product of the
concrete two-dimensional permutation cores. Zero multiplicity is allowed.

This supplies the finite-sum realization used by the product decomposition
in Aschbacher–Smith G.2.6(5), printed p.336, PDF p.347. The equivariance
proof reduces to pure tensors and `InvertedCubicTensor.tensorEquiv_symmetric`.
-/

public section

open InvertedCubicTensor
open scoped TensorProduct
namespace Representation.BinaryQuadraticPair.ProductDecomposition

variable {I : Type*} [AddCommGroup I] [Module F I] [FiniteDimensional F I]

private noncomputable def tensorToCopies :
    I ⊗[F] BinaryPermutation.core (Fin 3) ≃ₗ[F]
      (Fin (Module.finrank F I) → BinaryPermutation.core (Fin 3)) :=
  (_root_.TensorProduct.comm F I (BinaryPermutation.core (Fin 3))).trans
    ((_root_.TensorProduct.congr (LinearEquiv.refl F _) (Module.finBasis F I).equivFun).trans
      (_root_.TensorProduct.piScalarRight F F (BinaryPermutation.core (Fin 3)) _))

private theorem tensorToCopies_tmul (i : I) (n : BinaryPermutation.core (Fin 3)) :
    tensorToCopies (i ⊗ₜ[F] n) = fun j => (Module.finBasis F I).equivFun i j • n := by
  simp [tensorToCopies]

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (σ : Representation F S₃ V)

/-- The multiplicity is the dimension of the transposition-fixed subspace. -/
noncomputable abbrev naturalMultiplicity : ℕ := Module.finrank F (multiplicitySpace σ)

/-- Choosing a basis in the tensor multiplicity space realizes a finite sum. -/
noncomputable def naturalSumEquiv (h : ∀ v, σ cubic v = v → v = 0) :
    (Fin (naturalMultiplicity σ) → BinaryPermutation.core (Fin 3)) ≃ₗ[F] V :=
  (tensorToCopies (I := multiplicitySpace σ)).symm.trans (tensorEquiv σ h)

/-- The finite-sum equivalence intertwines the concrete natural action in every coordinate. -/
theorem naturalSumEquiv_equivariant (h : ∀ v, σ cubic v = v → v = 0)
    (g : S₃) (x : Fin (naturalMultiplicity σ) → BinaryPermutation.core (Fin 3)) :
    naturalSumEquiv σ h (fun j => BinaryPermutation.coreRepresentation (Fin 3) g (x j)) =
      σ g (naturalSumEquiv σ h x) := by
  obtain ⟨z, rfl⟩ := (tensorToCopies (I := multiplicitySpace σ)).surjective x
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    change naturalSumEquiv σ h 0 = 0
    exact map_zero _
  | tmul i n =>
    have he : (fun j => BinaryPermutation.coreRepresentation (Fin 3) g
        (tensorToCopies (i ⊗ₜ[F] n) j)) =
        tensorToCopies (i ⊗ₜ[F] BinaryPermutation.coreRepresentation (Fin 3) g n) := by
      simp only [tensorToCopies_tmul, map_smul]
    rw [he]
    simp only [naturalSumEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact tensorEquiv_symmetric σ h g i n
  | add x y hx hy =>
    change naturalSumEquiv σ h
      ((fun j => BinaryPermutation.coreRepresentation (Fin 3) g (tensorToCopies (x + y) j))) = _
    have he : (fun j => BinaryPermutation.coreRepresentation (Fin 3) g
        (tensorToCopies (x + y) j)) =
        (fun j => BinaryPermutation.coreRepresentation (Fin 3) g (tensorToCopies x j)) +
        (fun j => BinaryPermutation.coreRepresentation (Fin 3) g (tensorToCopies y j)) := by
      funext j
      simp only [map_add, Pi.add_apply]
    rw [he, map_add, hx, hy, map_add, map_add, map_add]

/-- Each natural summand contributes dimension two. -/
theorem naturalSum_finrank (h : ∀ v, σ cubic v = v → v = 0) :
    Module.finrank F V = 2 * naturalMultiplicity σ := by
  rw [← (naturalSumEquiv σ h).finrank_eq, Module.finrank_pi_fintype]
  simp [natural_finrank, mul_comm]

end Representation.BinaryQuadraticPair.ProductDecomposition
