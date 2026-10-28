module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Basis
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The explicit exterior marking of native F

Column masks specify the images of the ordered wedge basis in the original
native F basis. Both inverse equations are checked over the binary field.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Representation.SL5ExteriorSquare
open Representation.SL5TenDimensional

def fColumnMatrix (c : Fin 10 → ℕ) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun i j => if (c j).testBit i.val then 1 else 0

def markingMasks : Fin 10 → ℕ := ![2,4,54,89,27,14,454,3,904,640]
def markingMatrix := fColumnMatrix markingMasks
def inverseMarkingMatrix := fColumnMatrix ![129,1,2,35,179,180,25,889,803,377]
set_option maxRecDepth 10000 in
private theorem marking_inverse : markingMatrix * inverseMarkingMatrix = 1 := by decide +kernel
set_option maxRecDepth 10000 in
private theorem inverse_marking : inverseMarkingMatrix * markingMatrix = 1 := by decide +kernel

def markingChange : FC ≃ₗ[ZMod 2] FC :=
  { markingMatrix.mulVecLin with
    invFun := inverseMarkingMatrix.mulVec
    left_inv := fun v => by
      change inverseMarkingMatrix.mulVec (markingMatrix.mulVec v) = v
      rw [Matrix.mulVec_mulVec, inverse_marking, Matrix.one_mulVec]
    right_inv := fun v => by
      change markingMatrix.mulVec (inverseMarkingMatrix.mulVec v) = v
      rw [Matrix.mulVec_mulVec, marking_inverse, Matrix.one_mulVec] }

/-- The marking goes from the actual exterior power to the actual native group. -/
def exteriorParam : Multiplicative V ≃* F :=
  ((coordinates.trans markingChange).toAddEquiv.toMultiplicative).trans nativeParam

def exteriorMarking : F ≃* Multiplicative V := exteriorParam.symm

theorem exteriorParam_basis (i : Fin 10) :
    (exteriorParam (Multiplicative.ofAdd (basis i)) : Model) = fValue (markingMasks i) := by
  change (nativeParam (Multiplicative.ofAdd (markingMatrix.mulVec (coordinates (basis i)))) : Model) = _
  have hc : coordinates (basis i) = Pi.single i 1 := by
    funext j
    simpa only [coordinates, Pi.single_apply, eq_comm] using basis.equivFun_self i j
  rw [hc, Matrix.mulVec_single_one]
  exact nativeParam_mask _

open scoped IsMulCommutative
attribute [local instance] F_elementary

/-- The marking is linear on the canonical binary module of the native group. -/
def exteriorLinearMarking : Additive F ≃ₗ[ZMod 2] V :=
  { exteriorMarking.toAdditiveLeft with
    map_smul' := ZMod.map_smul exteriorMarking.toAdditiveLeft }

theorem exteriorLinearMarking_apply (x : F) :
    exteriorLinearMarking (Additive.ofMul x) = (exteriorMarking x).toAdd := rfl

end Janko4.LocalStructure.LinearFive
