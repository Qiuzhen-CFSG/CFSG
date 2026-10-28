module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Normalizes
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Marking

/-!
# The native normalizer acts by the specified exterior square

The two actual native conjugations are first identified in F's original basis.
A checked change-of-basis identity then identifies their actions with the
exterior squares of A0 and A1, with the same left-conjugation convention.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive.NativeNormalizer
open Cardinality KernelCount
open Representation Representation.SL5ExteriorSquare Representation.SL5TenDimensional
open Representation.SL5ExteriorSquare.TwoGeneratorRecognition
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localX localY

def naturalElement : Fin 2 → Representation.SL5TenDimensional.Group := ![A0,A1]

def nativeAction (i : Fin 2) : FC ≃ₗ[ZMod 2] FC :=
  BinaryConjugationSection.normalizerAction nativeParam.symm.toMonoidHom
    nativeParam.symm.bijective (normalizerElement i)

private theorem nativeAction_single (i : Fin 2) (j : Fin 10) :
    nativeAction i (Pi.single j 1) = maskVector (actionMasks i j) := by
  have hg : (nativeParam.symm (fGenerator j)).toAdd = Pi.single j 1 := by
    rw [← nativeParam_single, nativeParam.symm_apply_apply]
    rfl
  have hc : F.normalizerMonoidHom (normalizerElement i) (fGenerator j) =
      nativeParam (Multiplicative.ofAdd (maskVector (actionMasks i j))) := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, nativeParam_mask]
    exact element_conjugates i j
  have h := BinaryConjugationSection.normalizerAction_coordinates
    nativeParam.symm.toMonoidHom nativeParam.symm.bijective
      (normalizerElement i) (fGenerator j)
  change nativeAction i ((nativeParam.symm (fGenerator j)).toAdd) =
    (nativeParam.symm (F.normalizerMonoidHom (normalizerElement i) (fGenerator j))).toAdd at h
  simpa only [hg, hc, nativeParam.symm_apply_apply, toAdd_ofAdd] using h

theorem nativeAction_matrix (i : Fin 2) :
    (nativeAction i).toLinearMap = (fColumnMatrix (actionMasks i)).mulVecLin := by
  apply (Pi.basisFun (ZMod 2) (Fin 10)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change nativeAction i (Pi.single j 1) = (fColumnMatrix (actionMasks i)).mulVec (Pi.single j 1)
  rw [nativeAction_single, Matrix.mulVec_single_one]
  rfl

private theorem nativeAction_coordinates (i : Fin 2) (x : F) :
    (nativeParam.symm (F.normalizerMonoidHom (normalizerElement i) x)).toAdd =
      (fColumnMatrix (actionMasks i)).mulVec (nativeParam.symm x).toAdd := by
  have h := BinaryConjugationSection.normalizerAction_coordinates
    nativeParam.symm.toMonoidHom nativeParam.symm.bijective (normalizerElement i) x
  change nativeAction i (nativeParam.symm x).toAdd = _ at h
  have he := LinearMap.congr_fun (nativeAction_matrix i) (nativeParam.symm x).toAdd
  exact h.symm.trans he

set_option maxRecDepth 10000 in
private theorem matrix_intertwines (i : Fin 2) :
    fColumnMatrix (actionMasks i) * markingMatrix = markingMatrix * actionMatrix (naturalElement i) := by
  fin_cases i <;> decide +kernel

private theorem marking_coordinates (x : F) :
    (nativeParam.symm x).toAdd = markingMatrix.mulVec (coordinates (exteriorMarking x).toAdd) := by
  have h := exteriorParam.apply_symm_apply x
  change nativeParam (Multiplicative.ofAdd
    (markingMatrix.mulVec (coordinates (exteriorMarking x).toAdd))) = x at h
  exact (congrArg (fun y : F => (nativeParam.symm y).toAdd) h).symm.trans
    (by rw [nativeParam.symm_apply_apply, toAdd_ofAdd])

/-- Exact left exterior action, on every element of the original native F. -/
theorem exterior_conjugation (i : Fin 2) (x : F) :
    (exteriorMarking (F.normalizerMonoidHom (normalizerElement i) x)).toAdd =
      exteriorAction 2 (naturalElement i) (exteriorMarking x).toAdd := by
  apply coordinates.injective
  apply markingChange.injective
  change markingMatrix.mulVec (coordinates
    (exteriorMarking (F.normalizerMonoidHom (normalizerElement i) x)).toAdd) =
      markingMatrix.mulVec (coordinates
        (exteriorAction 2 (naturalElement i) (exteriorMarking x).toAdd))
  rw [← marking_coordinates, coordinates_action, Matrix.mulVec_mulVec,
    ← matrix_intertwines, ← Matrix.mulVec_mulVec, ← marking_coordinates]
  exact nativeAction_coordinates i x

end Janko4.LocalStructure.LinearFive.NativeNormalizer
