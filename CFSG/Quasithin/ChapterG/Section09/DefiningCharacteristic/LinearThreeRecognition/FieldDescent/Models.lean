module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.Models
public import Theory.Representation.SL3.BinaryFieldDescent.BaseChange

/-!
# Base change of the concrete SL₃ models

Coordinatewise coefficient extension identifies the extended natural action
with the matrix action after the specified field embedding. Combining two
such equivalences with distribution of scalar extension over tensors gives
the same identification for the literal Frobenius-twisted tensor.
The general dual comparison also applies to both models.

These comparisons implement the model step in GLS III, Remark 2.8.8 and
Example 2.8.10(c), used by G.9.3(8),(17).
-/

@[expose] public noncomputable section
open scoped TensorProduct MatrixGroups
open Representation

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Base change of the natural action, retaining the specified coefficient map. -/
noncomputable def naturalBaseChange (κ : F →+* F) :
    (extendScalars K (naturalOver F κ)).Equiv
      (naturalOver F ((algebraMap F K).comp κ)) :=
  .mk (TensorProduct.piScalarRight F K K (Fin 3)) (by
    intro g
    ext v i
    change (TensorProduct.piScalarRight F K K (Fin 3))
      ((1 : K) ⊗ₜ[F] (naturalOver F κ g (Pi.single v 1))) i =
      naturalOver F ((algebraMap F K).comp κ) g
        ((TensorProduct.piScalarRight F K K (Fin 3)) ((1 : K) ⊗ₜ[F] (Pi.single v 1))) i
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Algebra.smul_def, mul_one]
    change (algebraMap F K) (((g.val.map κ).mulVec (Pi.single v 1)) i) =
      ((g.val.map ((algebraMap F K).comp κ)).mulVec
        (fun j => (algebraMap F K) ((Pi.single v 1 : Fin 3 → F) j))) i
    simp [Matrix.mulVec, dotProduct])


/-- The identity coefficient map gives the literal natural action. -/
theorem naturalOver_id : naturalOver F (RingHom.id F) = specialLinearNatural 3 := by
  ext g v i
  rfl

/-- Base change of the literal natural action. -/
def naturalUntwistedBaseChange :
    (extendScalars K (specialLinearNatural (k := F) 3)).Equiv
      (naturalOver F (algebraMap F K)) := by
  simpa only [naturalOver_id, RingHom.comp_id] using
    naturalBaseChange (K := K) (RingHom.id F)

/-- Base change of the literal twisted tensor action. -/
def twistedTensorBaseChange (σ : F ≃+* F) :
    (extendScalars K (twistedTensor F σ)).Equiv
      (twistedTensorOver F (algebraMap F K) σ) :=
  (Representation.BinaryFieldDescent.tensorBaseChange _ _).trans
    (Representation.BinaryFieldDescent.tensorEquiv naturalUntwistedBaseChange
      (naturalBaseChange σ.toRingHom))

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
