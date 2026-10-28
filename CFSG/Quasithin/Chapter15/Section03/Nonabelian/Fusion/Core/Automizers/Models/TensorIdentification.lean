module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models.Actions
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The literal tensor product behind the lower matrix coordinates

Tensor-product distributivity identifies the tensor of two binary planes
with two-by-two binary matrices. Pure tensors become outer products, and
the external tensor of the two natural actions becomes X ↦ a X bᵀ.
Composing this equivalence with `LayerActions.lowerCoordinates` gives an
actual multiplicative equivalence to the tensor product, intertwining the
same common actor used on P/V.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the natural
Ω₄⁺(2) action in 15.3.53(1), printed p.1146, used in 15.3.59 on p.1150.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
open scoped TensorProduct
open Matrix Subgroup

abbrev NaturalPlane := Fin 2 → ZMod 2
abbrev NaturalTensor := NaturalPlane ⊗[ZMod 2] NaturalPlane

/-- Actual tensor-product coordinates, with rows indexed by the first factor. -/
def tensorMatrix : NaturalTensor ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  (TensorProduct.comm (ZMod 2) NaturalPlane NaturalPlane).trans
    (TensorProduct.piScalarRight (ZMod 2) (ZMod 2) NaturalPlane (Fin 2))

theorem tensorMatrix_tmul (v w : NaturalPlane) :
    tensorMatrix (v ⊗ₜ[ZMod 2] w) = Matrix.vecMulVec v w := by
  change TensorProduct.piScalarRight (ZMod 2) (ZMod 2) NaturalPlane (Fin 2)
    ((TensorProduct.comm (ZMod 2) NaturalPlane NaturalPlane) (v ⊗ₜ[ZMod 2] w)) = _
  rw [TensorProduct.comm_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]
  rfl

/-- The matrix action is exactly the external tensor of the natural actions. -/
theorem tensorMatrix_map (a : Actor) (z : NaturalTensor) :
    tensorMatrix (TensorProduct.map (Matrix.toLin' a.1.val) (Matrix.toLin' a.2.val) z) =
      a.1.val * tensorMatrix z * a.2.val.transpose := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    rw [TensorProduct.map_tmul, tensorMatrix_tmul, tensorMatrix_tmul,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose,
      Matrix.transpose_transpose]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mul_add, Matrix.add_mul]

namespace LayerActions
variable {G : Type*} [Group G] {I Y P V : Subgroup G}
variable {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
variable [(V.subgroupOf P).Normal] (d : LayerActions I Y P V hIP hIV)

/-- A literal tensor-product version of the lower coordinate equivalence. -/
def tensorCoordinates : V ≃* Multiplicative NaturalTensor :=
  d.lowerCoordinates.trans tensorMatrix.toAddEquiv.toMultiplicative.symm

theorem tensorCoordinates_compatible (i : I) (v : V) :
    d.tensorCoordinates (lowerAction I V hIV i v) = Multiplicative.ofAdd
      (TensorProduct.map (Matrix.toLin' (d.actor i).1.val) (Matrix.toLin' (d.actor i).2.val)
        (d.tensorCoordinates v).toAdd) := by
  apply Multiplicative.toAdd.injective
  apply tensorMatrix.injective
  change tensorMatrix (tensorMatrix.symm (d.lowerCoordinates (lowerAction I V hIV i v)).toAdd) =
    tensorMatrix (TensorProduct.map _ _ (tensorMatrix.symm (d.lowerCoordinates v).toAdd))
  rw [tensorMatrix.apply_symm_apply, tensorMatrix_map, tensorMatrix.apply_symm_apply]
  exact congrArg Multiplicative.toAdd (d.lower_compatible i v)

end LayerActions
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
