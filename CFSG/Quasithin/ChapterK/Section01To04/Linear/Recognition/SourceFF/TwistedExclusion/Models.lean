module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.FieldDescent
public import Theory.Representation.SL3.BinaryDefiningFactors.SmallPatterns

/-!
# Actual coefficient and graph twists of the tensor model

Precomposition retains each intertwiner. The dot product identifies the
inverse-transpose twist with the dual natural action; tensoring these
pairings identifies the graph twist of the whole tensor with its dual.
This permits the dual alternative in K.3.2 to use the same Hermitian model
after precomposing the supplied central cover.

Source: Aschbacher–Smith, K.3.2(c), printed pp.454–456.
-/

@[expose] public noncomputable section
open Representation
open scoped MatrixGroups TensorProduct
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.TwistedExclusion
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

def precomposeEquiv {F D G V W : Type*} [Field F] [Group D] [Group G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F G V} {τ : Representation F G W}
    (e : ρ.Equiv τ) (f : D →* G) : Representation.Equiv (ρ.comp f) (τ.comp f) :=
  .mk e.toLinearEquiv (fun d => e.isIntertwining' (f d))

def graph (F : Type*) [Field F] : MulAut SL(3,F) where
  toFun := Matrix.SpecialLinearGroup.inverseTranspose
  invFun := Matrix.SpecialLinearGroup.inverseTranspose
  left_inv g := by
    change ((Matrix.SpecialLinearGroup.inverseTranspose g)⁻¹).transpose = g
    rw [← map_inv]
    change ((g⁻¹)⁻¹).transpose.transpose = g
    rw [inv_inv]
    apply Subtype.ext
    rfl
  right_inv g := by
    change ((Matrix.SpecialLinearGroup.inverseTranspose g)⁻¹).transpose = g
    rw [← map_inv]
    change ((g⁻¹)⁻¹).transpose.transpose = g
    rw [inv_inv]
    apply Subtype.ext
    rfl
  map_mul' := map_mul _

variable {F K : Type*} [Field F] [Field K]

def naturalOverGraphDual (ι : F →+* K) :
    Representation.Equiv ((naturalOver F ι).comp (graph F).toMonoidHom) (naturalOver F ι).dual :=
  .mk (dotProductEquiv K (Fin 3)) (by
    intro g
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro v
    change (((g⁻¹).val.transpose.map ι).mulVec w) ⬝ᵥ v =
      w ⬝ᵥ (((g⁻¹).val.map ι).mulVec v)
    change (((g⁻¹).val.map ι).transpose.mulVec w) ⬝ᵥ v =
      w ⬝ᵥ (((g⁻¹).val.map ι).mulVec v)
    rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec])

def tensorOverGraphDual [CharP K 2] (ι : F →+* K) (σ : F ≃+* F) :
    Representation.Equiv ((twistedTensorOver F ι σ).comp (graph F).toMonoidHom)
      (twistedTensorOver F ι σ).dual :=
  (BinaryFieldDescent.tensorEquiv (naturalOverGraphDual ι)
    (naturalOverGraphDual (ι.comp σ.toRingHom))).trans
      (Representation.SL3.BinaryDefiningFactors.dualTensorEquiv _ _)

def tensorOverDualGraph [CharP K 2] (ι : F →+* K) (σ : F ≃+* F) :
    Representation.Equiv ((twistedTensorOver F ι σ).dual.comp (graph F).toMonoidHom)
      (twistedTensorOver F ι σ) :=
  .mk (tensorOverGraphDual ι σ).symm.toLinearEquiv (by
    intro g
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show graph F (graph F g) = g from (graph F).left_inv g] using
      (tensorOverGraphDual ι σ).symm.isIntertwining' (graph F g))

end CFSG.Quasithin.ChapterK.Linear.Recognition.TwistedExclusion
