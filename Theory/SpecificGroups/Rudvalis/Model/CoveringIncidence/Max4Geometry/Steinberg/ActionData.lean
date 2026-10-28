module
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Steinberg.Actor
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Coordinates
import Mathlib.Tactic.FinCases

/-!
# Word coordinates for the max4 Steinberg calculation

The conjugate words are proposed finite certificates in the eleven shared
words. The original exploration used diagonal coordinates (a00,a22); the
published Steinberg model uses (a00,a11), so the last row of the intertwiner
has been replaced by the sum of its last two rows. The inverse and the two
intertwining equations are checked here in the actual trace-zero model.
The permutation word identities remain a separate certificate obligation.

Source: Aschbacher--Smith I.2.2(7), printed pp.412--413; GLS3 Table 5.3r.
The word conventions and ATLAS attribution are inherited from Max4Geometry.Words.
-/

open Subgroup Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open BinaryLinearThree BinaryLinearThree.IrreducibleCatalogue
namespace Rudvalis.CoveringIncidence.Max4Steinberg

@[expose] public def conjugateWord : Fin 2 → Fin 11 → List (Fin 11) :=
  ![![[0,1,3,4,8,9,10],
    [1,5,6,9],
    [2,3,4,7,10],
    [1,3,5,7,8,10],
    [1,4,6,7,9,10],
    [5,8,10],
    [6],
    [5,6,7,9],
    [8],
    [8,9,10],
    [10]],
    ![[3,5,8,9,10],
    [1,2,4,9],
    [1,6,7,8],
    [0,2,3,4,6,10],
    [6,7,9],
    [7,9,10],
    [2,7,8],
    [1,4,5,6,7],
    [9],
    [8,9],
    [9,10]]]

/-- A finite obligation on the original Rudvalis carrier, with left conjugation. -/
@[expose] public def ConjugateWordIdentities : Prop :=
  ∀ (i : Fin 2) (j : Fin 11),
    (actorGenerator i : Model) * Max4Words.generator j * (actorGenerator i : Model)⁻¹ =
      ((conjugateWord i j).map Max4Words.generator).prod

/-- The final three words must match the existing marked generators literally. -/
@[expose] public def CentralWordIdentities : Prop :=
  ∀ i : Fin 3, Max4Words.generator ⟨8 + i.val, by omega⟩ =
    (markedBasis (![2,1,0] i) : Model)

@[expose] public def intertwinerMatrix : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0,1,0,1,1,1,0,0;
    0,0,1,0,0,0,0,1;
    1,0,0,1,1,0,0,0;
    0,0,1,1,1,0,0,0;
    0,1,0,1,1,0,0,0;
    1,0,0,1,0,1,1,0;
    0,1,0,0,0,0,0,0;
    0,0,0,0,1,0,0,0]

private def inverseMatrix : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![0,0,1,0,1,0,1,0;
    0,0,0,0,0,0,1,0;
    0,0,0,1,1,0,1,0;
    0,0,0,0,1,0,1,1;
    0,0,0,0,0,0,0,1;
    1,0,0,0,1,0,0,0;
    1,0,1,0,1,1,0,1;
    0,1,0,1,1,0,1,0]

private theorem inverse_left : inverseMatrix * intertwinerMatrix = 1 := by decide
private theorem inverse_right : intertwinerMatrix * inverseMatrix = 1 := by decide

public def intertwinerLinear : Eight ≃ₗ[ZMod 2] Eight :=
  LinearEquiv.ofLinearMap intertwinerMatrix.toLin' inverseMatrix.toLin'
    (by rw [← Matrix.toLin'_mul, inverse_right, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, inverse_left, Matrix.toLin'_one])

public theorem intertwinerLinear_apply (v : Eight) :
    intertwinerLinear v = intertwinerMatrix.mulVec v := by rfl

/-- All eleven word images, with the three center words sent to zero. -/
@[expose] public def wordVector (j : Fin 11) : Eight :=
  if h : j.val < 8 then intertwinerMatrix.mulVec (Pi.single ⟨j.val, h⟩ 1) else 0

public noncomputable def wordImage (j : Fin 11) : Steinberg :=
  coordinates.symm (wordVector j)

public theorem wordImage_eq (j : Fin 11) :
    wordImage j = coordinates.symm (wordVector j) := by rfl

private theorem coordinates_action (g : Group) (v : Eight) :
    coordinates (S g (coordinates.symm v)) =
      readMatrix (g.val * matrixOf v * g.val.adjugate) := by
  change readMatrix (LinearMap.toMatrix'
    (g.val.toLin' ∘ₗ (matrixOf v).toLin' ∘ₗ g.val.adjugate.toLin')) = _
  rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, LinearMap.toMatrix'_toLin']
  exact congrArg readMatrix (Matrix.mul_assoc _ _ _).symm

private theorem vector_certificate (i : Fin 2) (j : Fin 11) :
    readMatrix ((naturalGenerator i).val * matrixOf (wordVector j) *
      (naturalGenerator i).val.adjugate) =
        ((conjugateWord i j).map wordVector).sum := by
  simp only [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;> decide

/-- The saved intertwiner has the required action in the literal adjoint module. -/
public theorem wordImage_action (i : Fin 2) (j : Fin 11) :
    S (naturalGenerator i) (wordImage j) =
      ((conjugateWord i j).map wordImage).sum := by
  apply coordinates.injective
  rw [wordImage, coordinates_action, vector_certificate]
  simp only [map_list_sum, List.map_map, Function.comp_def, wordImage,
    LinearEquiv.apply_symm_apply]

end Rudvalis.CoveringIncidence.Max4Steinberg
