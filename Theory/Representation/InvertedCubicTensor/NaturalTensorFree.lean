module
public import Theory.Representation.InvertedCubicTensor.NaturalFactors
public import Theory.Representation.TensorFunctionCoordinates
/-!
# Cubic fixed vectors in the literal natural tensor module

A cubic permutation fixes no nonzero vector of the binary natural plane.
Finite multiplicity coordinates prove the same assertion for a natural
tensor realization, retaining its actual equivariant linear equivalence.

Source application: Aschbacher--Smith 12.8.9(3) and 14.3.18(4), pp.853,996.
-/

@[expose] public section
noncomputable section
open InvertedCubicTensor
open scoped TensorProduct
namespace InvertedCubicTensor
private instance : Fintype NaturalPlane :=
  @Subtype.fintype _ _
    (fun x => inferInstanceAs (Decidable (∑ i : Fin 3, x i = 0)))
    (inferInstance : Fintype (Fin 3 → ZMod 2))
theorem naturalPlane_cubic_fixed_zero (v : NaturalPlane)
    (hv : BinaryPermutation.coreRepresentation (Fin 3) cubic v=v) : v=0 := by
  have cert : ∀ v : NaturalPlane,
      BinaryPermutation.coreRepresentation (Fin 3) cubic v=v→v=0 := by
    decide +kernel
  exact cert v hv
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
theorem cubic_fixed_zero_of_natural_tensor
    (σ : Representation (ZMod 2) S₃ W) [Module.Finite (ZMod 2) (multiplicitySpace σ)]
    (j : multiplicitySpace σ ⊗[ZMod 2] NaturalPlane ≃ₗ[ZMod 2] W)
    (hj : ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
      (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z)=σ a (j z))
    (w : W) (hw : σ cubic w=w) : w=0 := by
  let q := Representation.tensorFunctionCoordinates j
  apply q.injective
  apply funext
  intro i
  have he := Representation.tensorFunctionCoordinates_equivariant
    (BinaryPermutation.coreRepresentation (Fin 3)) σ j hj cubic w i
  rw [hw] at he
  simpa only [map_zero, Pi.zero_apply] using naturalPlane_cubic_fixed_zero (q w i) he.symm
end InvertedCubicTensor
