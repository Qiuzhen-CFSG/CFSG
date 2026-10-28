module

public import Theory.Representation.ExtendScalars
public import Theory.Representation.AbelianAllWeights
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod

/-!
# Frobenius preserves weights of a binary scalar extension

Tensor the field Frobenius with the identity on the binary vector space.
This map is injective, semilinear, and commutes with the extended action.
It therefore takes a nonzero character vector to a nonzero vector for the
squared character. The binary descent is essential to the commutation.

This is the scalar-descent ingredient of the seven-plane degree argument
for the triality endpoint in Aschbacher--Smith, G.9.3, printed p.356.
-/

public section

open scoped TensorProduct
namespace Representation.BinarySevenPlaneDegree
variable {E G V : Type*} [Field E] [CharP E 2] [Algebra (ZMod 2) E]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private noncomputable def frobTensor : E ⊗[ZMod 2] V →ₗ[ZMod 2] E ⊗[ZMod 2] V :=
  ((frobenius E 2).toAddMonoidHom.toZModLinearMap 2).rTensor V

private lemma frobTensor_injective : Function.Injective (frobTensor (E := E) (V := V)) :=
  Module.Flat.rTensor_preserves_injective_linearMap _ (frobenius_inj E 2)

private lemma frobTensor_smul (a : E) (v : E ⊗[ZMod 2] V) :
    frobTensor (a • v) = a ^ 2 • frobTensor v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [frobTensor, TensorProduct.smul_tmul', LinearMap.rTensor_tmul]
    change ((a * x) ^ 2) ⊗ₜ[ZMod 2] y = a ^ 2 • ((x ^ 2) ⊗ₜ[ZMod 2] y)
    rw [mul_pow, TensorProduct.smul_tmul']
    rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private lemma frobTensor_commute (rho : Representation (ZMod 2) G V) (g : G)
    (v : E ⊗[ZMod 2] V) :
    frobTensor (rho.extendScalars E g v) = rho.extendScalars E g (frobTensor v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Squaring preserves occurring characters of an actual binary scalar extension. -/
theorem frobenius_occurs (rho : Representation (ZMod 2) G V) (chi : G →* Eˣ)
    (hchi : (rho.extendScalars E).characterWeightSpace chi ≠ ⊥) :
    (rho.extendScalars E).characterWeightSpace (chi ^ 2) ≠ ⊥ := by
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hchi
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨frobTensor v, ?_, ?_⟩
  · simp only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hv ⊢
    intro g
    rw [← frobTensor_commute, hv g, frobTensor_smul]
    rfl
  · intro hz
    exact hn (frobTensor_injective (hz.trans (map_zero _).symm))
end Representation.BinarySevenPlaneDegree
