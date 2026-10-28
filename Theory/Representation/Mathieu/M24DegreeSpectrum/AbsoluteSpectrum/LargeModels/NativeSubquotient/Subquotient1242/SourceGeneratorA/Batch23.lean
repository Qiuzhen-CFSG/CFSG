module
public meta import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.GapLiteral
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.SourceGeneratorA.Batch22
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.Matrices

/-!
# Literal sourceGeneratorA matrix identity

Separate mask and product checks run in bounded sequential batches.
The saved witness is unchanged; see source/README.md for provenance.
-/

set_option Elab.async false
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
open Degree220Pair.NativeActions.CertificatePacked Packed
open Degree320Pair.MatrixCertificates.TraceRows

namespace SourceGeneratorAChecks

private noncomputable def left184Row0Part1 : List ℕ := native_gaps% "2,1,5,0,0,1,0,0,4,0,1,1,0,1,1,0,0,1,1,3,1,1,0,0,0,2,5,0,0,3,2,0,0,4,0,4,2,4,0,0,0,1,0,0,1,1,0,0,0,11,1,2,2,0,3,0,2,1,1,2,0,0,0,4,4,0,1,2,0,2,0,1,1,2,0,0,6,1,3,1,1,1" [[]]

private noncomputable def left184Row0Part0 : List ℕ := native_gaps% "1472,1,0,0,1,2,0,0,0,0,0,2,0,0,3,0,0,3,0,6,1,1,3,2,1,0,0,2,0,0,2,0,2,2,0,0,1,0,0,0,2,0,0,4,0,12,1,5,3,1,4,1,0,3,5,0,0,0,0,1,1,0,1,0,6,1,4,0,0,0,1,0,1,5,0,1,1,0,0,0,4,1,1,3,0,0,0,0,1,0,2,0,0,0,0,0,2,3,1,0,0,2,0,0,0,0,0,0,0,0,2,1,1,0,0,2,0,0,8,0,2,0,1,0,2,6,0,2" [left184Row0Part1]

private noncomputable def left184Row0 : List ℕ := left184Row0Part0

private noncomputable def left184Row1Part1 : List ℕ := native_gaps% "2,0,0,0,0,3,4,0,2,0,0,0,0,4,1,2,0,3,0,1,0,1,1,3,3,1,0,5,0,0,1,0,0,0,1,0,2,1,3,3,1,6,2,1,1,0,1,1,0,0,0,0,0,7,0,1,2,0,0,0,0,4,0,0,1,0,0,2,0,0,6,7,1,1,0,1,1,1,1,2,1,0,1,2,2,1,6,0,0,0" [[]]

private noncomputable def left184Row1Part0 : List ℕ := native_gaps% "1473,4,2,0,0,0,0,4,3,2,0,0,3,2,1,0,0,1,1,0,0,3,1,5,0,0,0,0,1,0,0,2,1,2,0,1,4,1,0,1,0,0,1,1,0,1,1,5,0,0,1,0,0,0,0,3,4,2,1,0,0,4,0,3,0,1,0,0,1,0,0,0,1,0,2,4,0,1,0,3,0,3,3,2,2,3,0,2,1,1,3,0,0,4,1,2,0,0,0,1,2,0,2,0,0,0,0,0,0,0,0,0,1,1,4,0,0,1,0,0,2,0,1,0,0,0,1,1" [left184Row1Part1]

private noncomputable def left184Row1 : List ℕ := left184Row1Part0

private noncomputable def leftGaps184 : List (List ℕ) := [left184Row0, left184Row1]

private noncomputable def right184Row0Part5 : List ℕ := native_gaps% "1,1,1,0,1,0,0,0,0,0,4,0,0,0,0,1,2,1,1,0,3,0,0,1,1,1,0,2,6,3,0,0,1,1,2,0,1" [[]]

private noncomputable def right184Row0Part4 : List ℕ := native_gaps% "3,0,1,2,1,0,0,0,2,0,0,0,0,4,2,2,1,1,0,0,0,2,0,1,1,3,0,0,7,0,0,3,1,2,0,1,0,1,1,0,1,0,2,0,0,1,1,0,1,0,0,1,0,6,0,0,0,1,3,0,0,3,1,0,0,0,0,1,0,0,2,2,2,2,4,1,1,1,0,4,0,1,0,0,0,3,2,0,1,1,0,0,2,3,0,1,2,1,0,0,0,1,1,0,1,0,0,4,1,1,0,2,1,0,0,0,5,5,0,0,2,1,0,0,1,0,4,2" [right184Row0Part5]

private noncomputable def right184Row0Part3 : List ℕ := native_gaps% "1,2,1,1,0,0,4,0,1,0,1,0,0,1,0,0,0,1,0,5,4,0,0,0,2,0,2,2,2,0,1,0,1,1,0,0,0,1,0,0,1,0,1,0,0,2,0,1,0,0,2,0,1,1,1,1,1,0,0,0,2,2,0,0,3,0,1,0,0,0,0,0,0,3,1,7,2,1,1,1,1,1,0,1,0,0,0,0,1,0,0,0,0,1,1,1,1,0,1,0,5,0,0,1,1,2,1,0,0,0,3,0,0,0,0,0,1,1,1,0,1,1,0,1,2,2,0,3" [right184Row0Part4]

private noncomputable def right184Row0Part2 : List ℕ := native_gaps% "0,0,1,0,0,1,1,0,0,0,2,0,0,1,0,1,0,0,1,0,0,0,0,2,3,0,0,1,3,0,4,0,0,0,0,0,0,2,1,0,0,0,0,0,2,0,0,1,1,0,0,0,0,0,0,0,0,1,1,0,1,1,1,1,6,0,0,0,0,1,2,0,0,1,0,1,0,0,1,0,1,1,0,1,1,1,1,1,0,0,2,0,2,1,0,3,0,0,0,1,2,3,5,1,2,1,1,0,2,0,0,0,0,2,1,4,0,0,0,3,0,0,0,1,2,5,0,0" [right184Row0Part3]

private noncomputable def right184Row0Part1 : List ℕ := native_gaps% "1,0,0,0,0,0,0,0,2,0,0,1,1,3,0,0,3,4,0,0,3,0,2,1,0,3,1,0,1,1,2,0,1,0,0,1,0,0,2,0,0,0,1,1,0,1,1,3,3,0,1,0,3,1,1,3,1,0,2,1,1,0,0,2,1,5,0,1,1,1,0,0,0,0,0,0,0,0,0,5,0,1,7,1,0,3,1,0,0,0,4,3,1,0,0,0,0,0,0,1,3,8,0,2,0,0,0,0,2,2,1,0,2,1,0,1,0,0,0,2,9,0,5,2,1,1,0,1" [right184Row0Part2]

private noncomputable def right184Row0Part0 : List ℕ := native_gaps% "1,1,0,3,1,1,1,2,1,2,5,3,0,0,0,5,1,0,0,0,0,5,1,0,1,2,1,0,7,1,1,2,0,1,2,3,0,0,2,10,0,0,0,0,0,1,0,5,0,3,3,1,76,21,0,0,0,0,1,1,0,0,0,1,0,0,2,1,2,0,0,3,0,0,0,4,9,4,0,9,0,7,1,9,0,0,1,1,5,7,0,0,2,0,2,0,0,2,4,4,1,1,0,2,0,2,6,0,0,0,4,2,0,3,0,1,2,0,0,1,0,3,0,0,0,2,0,0" [right184Row0Part1]

private noncomputable def right184Row0 : List ℕ := right184Row0Part0

private noncomputable def right184Row1Part5 : List ℕ := native_gaps% "1,0,1,0,1,3,1,0,0,2,0,1,5,0,0,0,0,0,0,0,0,1,1,0,0,1,0,3,0,0,1,0,0,0,0,3,0,0,0,1,1,5,0" [[]]

private noncomputable def right184Row1Part4 : List ℕ := native_gaps% "0,2,0,2,2,1,0,0,1,0,1,1,0,0,1,0,0,0,1,0,0,1,0,2,0,3,2,1,2,0,0,1,0,8,0,0,1,3,0,0,0,0,0,1,3,0,0,3,0,0,1,0,1,5,0,3,1,1,0,1,2,4,2,3,0,2,0,0,0,2,4,0,0,0,1,0,0,0,0,0,0,5,0,0,0,0,1,2,0,0,1,4,2,0,1,2,4,0,0,2,1,0,0,3,1,0,0,2,3,2,0,0,0,4,3,3,0,0,0,1,5,0,2,1,1,6,0,0" [right184Row1Part5]

private noncomputable def right184Row1Part3 : List ℕ := native_gaps% "0,1,0,2,1,0,0,2,2,1,0,1,2,1,0,0,0,0,2,0,0,1,5,2,0,0,5,1,0,0,0,0,4,2,0,2,0,3,4,0,1,3,0,1,1,1,0,3,0,1,1,0,0,1,2,0,0,0,3,0,2,3,0,0,2,2,2,0,1,2,0,0,2,2,1,0,0,0,0,5,0,2,7,0,1,0,0,0,3,0,2,0,0,0,1,0,0,0,1,2,0,1,0,1,0,3,0,3,1,0,2,0,0,0,0,0,0,0,0,1,2,0,2,0,0,2,0,0" [right184Row1Part4]

private noncomputable def right184Row1Part2 : List ℕ := native_gaps% "0,0,2,0,1,0,3,0,1,3,0,3,2,0,0,0,7,1,0,0,1,0,1,2,0,0,0,2,0,0,2,2,1,0,0,0,0,0,0,0,0,0,2,1,2,1,0,0,0,0,2,0,1,1,3,0,0,1,2,0,0,0,0,1,5,1,0,2,0,1,1,4,5,0,0,1,0,4,2,4,0,0,0,3,0,0,0,0,2,0,1,0,0,1,2,0,8,0,0,8,0,1,0,0,0,0,1,0,0,2,0,1,0,0,1,4,3,1,0,0,0,0,0,0,2,0,1,0" [right184Row1Part3]

private noncomputable def right184Row1Part1 : List ℕ := native_gaps% "3,2,0,0,1,0,0,0,1,0,1,5,0,1,0,0,1,1,1,0,1,0,0,0,0,1,0,1,0,0,1,0,0,1,0,1,0,0,1,0,0,2,4,0,0,1,0,0,2,2,1,1,7,1,0,1,0,1,1,0,1,3,3,0,0,0,6,3,3,5,1,4,2,1,3,1,0,2,0,4,1,0,0,0,0,0,2,0,2,2,1,0,0,0,1,1,1,4,4,1,1,2,1,0,1,2,0,0,0,4,0,0,3,4,1,5,2,0,3,0,0,2,0,2,0,2,1,0" [right184Row1Part2]

private noncomputable def right184Row1Part0 : List ℕ := native_gaps% "0,2,0,4,0,1,0,1,0,0,0,2,0,1,2,0,0,0,0,4,0,2,1,1,2,0,0,1,2,0,0,4,2,1,1,0,2,0,0,1,0,0,1,2,2,1,0,0,2,0,3,3,3,0,0,1,0,0,2,4,0,1,1,0,0,0,1,76,0,0,0,20,0,2,0,4,0,0,1,4,0,0,4,1,0,0,2,0,0,0,0,1,2,7,0,2,1,3,0,5,0,9,0,2,0,0,1,0,0,2,0,0,0,1,4,0,0,2,1,0,1,0,3,1,2,0,0,0" [right184Row1Part1]

private noncomputable def right184Row1 : List ℕ := right184Row1Part0

private noncomputable def rightGaps184 : List (List ℕ) := [right184Row0, right184Row1]

private theorem leftMask184 :
    (leftGaps184.map gapMask == (embeddingTransposeRows.drop 1472).take 8) = true := by
  decide +kernel

private theorem rightMask184 :
    (rightGaps184.map gapMask == (sourceTransposeA.drop 1472).take 8) = true := by
  decide +kernel

private theorem products184 :
    (leftGaps184.map (gapRow ambientTransposeA) == rightGaps184.map (gapRow embeddingTransposeRows)) = true := by
  decide +kernel

theorem block184 :
    checkEqualProducts ambientTransposeA embeddingTransposeRows
      ((embeddingTransposeRows.drop 1472).take 8) ((sourceTransposeA.drop 1472).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask184) (beq_iff_eq.mp rightMask184)
    (beq_iff_eq.mp products184)

end SourceGeneratorAChecks
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
