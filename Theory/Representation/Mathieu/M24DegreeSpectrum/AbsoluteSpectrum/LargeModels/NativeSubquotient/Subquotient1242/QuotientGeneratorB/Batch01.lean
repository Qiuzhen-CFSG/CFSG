module
public meta import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.GapLiteral
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.QuotientGeneratorB.Batch00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.Matrices

/-!
# Literal quotientGeneratorB matrix identity

Separate mask and product checks run in bounded sequential batches.
The saved witness is unchanged; see source/README.md for provenance.
-/

set_option Elab.async false
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
open Degree220Pair.NativeActions.CertificatePacked Packed
open Degree320Pair.MatrixCertificates.TraceRows

namespace QuotientGeneratorBChecks

private noncomputable def left008Row0Part0 : List ℕ := native_gaps% "3,0,0,0,2,1,1,2,2,0,2,0,1,0,0,0,2,3,1,0,0,0,1,1,0,0,1,0,0,1,0,4,0,2,0,1,0,1,0,0,1,0,2,1,0,0,0,5,0,0,0,0,2,0,0,0,0,1,1,0,1,1,0,0,0,4,1,6,0,0,0,0,3,1,0,0,0,1,2,4,0,0,0,0,1,1,0,0,8,1,1,1,1,2,0,0,0,1,0,0,1,1,0,3,1,0,0,3,2,0,0,7,0,0,0,0,0,7,0" [[]]

private noncomputable def left008Row0 : List ℕ := left008Row0Part0

private noncomputable def left008Row1Part0 : List ℕ := native_gaps% "0,0,0,0,2,0,1,0,0,1,0,1,0,0,1,1,0,0,2,1,0,3,2,0,1,1,1,1,0,0,0,0,3,1,2,0,0,1,0,1,2,0,2,0,1,0,0,2,1,0,0,1,3,0,2,0,0,0,0,0,3,0,0,0,0,0,1,0,2,0,0,1,0,0,3,0,1,0,1,4,0,1,0,0,1,1,0,2,2,0,0,2,1,5,0,1,0,2,0,4,1,0,0,1,0,0,0,0,1,0,6,5,1,0,5,1,0,1,3,0,1,2,0" [[]]

private noncomputable def left008Row1 : List ℕ := left008Row1Part0

private noncomputable def left008Row2Part1 : List ℕ := native_gaps% "1,0,0,0,0" [[]]

private noncomputable def left008Row2Part0 : List ℕ := native_gaps% "0,1,6,1,0,2,0,0,2,0,0,2,1,2,0,0,0,1,2,0,0,2,1,2,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0,3,1,0,0,0,0,1,0,1,0,0,1,4,1,5,0,0,0,1,0,1,0,0,5,1,1,0,2,0,0,0,0,1,0,0,0,0,2,1,1,0,0,0,0,1,0,1,0,0,1,3,1,2,2,0,0,0,0,2,1,0,1,0,0,1,0,2,1,0,1,4,0,3,0,0,3,0,0,1,0,0,0,0,0,0,0,3,3,0" [left008Row2Part1]

private noncomputable def left008Row2 : List ℕ := left008Row2Part0

private noncomputable def left008Row3Part0 : List ℕ := native_gaps% "1,0,2,1,0,1,0,0,0,0,0,1,1,0,0,2,0,0,0,0,2,0,0,2,4,1,1,1,3,0,1,2,0,0,0,1,0,0,2,0,0,0,0,2,1,2,2,0,0,0,0,0,3,0,0,1,0,2,6,1,3,0,0,2,3,2,0,1,0,2,1,0,1,5,0,0,1,0,1,3,1,0,1,0,1,1,0,0,0,1,0,0,0,0,1,1,0,0,1,0,1,1,0,1,4,1,4,0,2,0,1,0,1,3,1,4,0,5,0,1" [[]]

private noncomputable def left008Row3 : List ℕ := left008Row3Part0

private noncomputable def left008Row4Part0 : List ℕ := native_gaps% "1,9,1,0,1,1,0,0,0,2,0,1,0,0,0,1,1,0,0,0,1,1,1,2,2,2,3,2,3,6,4,2,0,8,1,0,0,1,1,3,0,4,0,1,1,2,3,0,2,0,0,0,1,3,0,0,0,0,0,3,4,1,0,2,3,0,0,0,0,3,3,0,1,0,0,0,1,0,1,0,1,0,1,0,2,1,2,2,1,1,0,0,0,0,0,0,0,8,2,0,0,0,3,1,1" [[]]

private noncomputable def left008Row4 : List ℕ := left008Row4Part0

private noncomputable def left008Row5Part0 : List ℕ := native_gaps% "1,0,0,0,1,1,1,0,0,1,1,3,1,0,0,1,1,2,0,1,4,1,0,4,0,2,0,1,0,2,3,0,1,2,3,1,1,0,0,0,2,2,0,1,0,3,0,0,2,2,0,0,0,0,0,3,0,0,3,3,0,1,0,1,0,0,1,0,0,0,1,0,1,0,1,0,1,0,0,1,0,7,2,1,3,1,2,1,2,0,0,0,0,0,0,2,1,0,1,0,0,1,2,0,1,2,0,0,2,1,1,0,2,2,0,0,0,0,0,0,0,1,2" [[]]

private noncomputable def left008Row5 : List ℕ := left008Row5Part0

private noncomputable def left008Row6Part0 : List ℕ := native_gaps% "0,0,1,1,0,0,0,1,0,0,0,0,0,0,1,1,0,0,2,4,0,0,1,0,0,0,1,1,0,1,0,0,1,0,1,2,0,1,0,0,0,1,0,1,3,0,0,0,0,3,0,0,2,0,4,3,0,1,2,4,0,2,1,1,2,1,1,4,1,0,3,0,0,3,2,2,0,1,4,1,0,0,0,1,0,2,1,2,0,0,0,0,2,2,1,0,0,0,2,4,0,2,0,2,3,0,0,0,0,0,2,3,0,0,0,0,1,1,0,0,2,2,0" [[]]

private noncomputable def left008Row6 : List ℕ := left008Row6Part0

private noncomputable def left008Row7Part0 : List ℕ := native_gaps% "0,5,2,0,1,2,1,1,0,0,1,0,0,0,2,0,3,2,0,1,0,0,0,1,6,0,0,4,4,1,2,0,0,0,3,0,0,3,0,0,1,0,0,2,2,3,0,0,5,1,0,0,0,0,0,3,0,0,2,0,1,3,2,1,0,0,3,2,3,1,5,2,0,0,0,1,0,0,2,2,1,1,0,3,1,1,0,7,0,0,0,2,0,0,0,1,0,0,3,3,1,1,0,0,0,0,3,1,2" [[]]

private noncomputable def left008Row7 : List ℕ := left008Row7Part0

private noncomputable def leftGaps008 : List (List ℕ) := [left008Row0, left008Row1, left008Row2, left008Row3, left008Row4, left008Row5, left008Row6, left008Row7]

private noncomputable def right008Row0 : List ℕ := []

private noncomputable def right008Row1 : List ℕ := []

private noncomputable def right008Row2 : List ℕ := []

private noncomputable def right008Row3 : List ℕ := []

private noncomputable def right008Row4 : List ℕ := []

private noncomputable def right008Row5 : List ℕ := []

private noncomputable def right008Row6 : List ℕ := []

private noncomputable def right008Row7 : List ℕ := []

private noncomputable def rightGaps008 : List (List ℕ) := [right008Row0, right008Row1, right008Row2, right008Row3, right008Row4, right008Row5, right008Row6, right008Row7]

private theorem leftMask008 :
    (leftGaps008.map gapMask == (sourceTransposeB.drop 64).take 8) = true := by
  decide +kernel

private theorem rightMask008 :
    (rightGaps008.map gapMask == (quotientTransposeRows.drop 64).take 8) = true := by
  decide +kernel

private theorem products008 :
    (leftGaps008.map (gapRow quotientTransposeRows) == rightGaps008.map (gapRow targetB)) = true := by
  decide +kernel

theorem block008 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 64).take 8) ((quotientTransposeRows.drop 64).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask008) (beq_iff_eq.mp rightMask008)
    (beq_iff_eq.mp products008)

private noncomputable def left009Row0Part0 : List ℕ := native_gaps% "3,0,0,2,1,3,0,7,2,1,0,0,1,1,0,0,0,4,1,1,1,0,3,1,0,1,0,1,1,1,4,0,3,2,1,1,0,3,0,0,0,0,0,1,0,0,1,0,1,0,2,1,0,3,2,1,0,5,2,1,6,0,0,0,0,0,0,0,3,0,2,0,1,0,1,0,0,3,4,0,0,1,0,2,1,0,0,2,0,0,0,0,5,3,2,1,1,3,1,1,5,1,0,0,0,1,1,1,0,0" [[]]

private noncomputable def left009Row0 : List ℕ := left009Row0Part0

private noncomputable def left009Row1Part1 : List ℕ := native_gaps% "4,1,0,0,0,1" [[]]

private noncomputable def left009Row1Part0 : List ℕ := native_gaps% "1,2,4,2,0,1,0,0,1,2,0,0,1,6,4,1,0,1,0,0,0,0,0,2,0,1,2,0,0,2,1,4,1,0,0,0,0,0,0,0,0,0,4,1,0,0,5,1,0,0,0,1,1,0,0,0,0,0,2,0,1,0,0,0,0,3,0,1,2,2,0,0,0,4,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,1,0,1,0,0,0,0,1,2,0,0,0,0,3,0,2,0,1,0,0,0,3,0,0,0,0,0,1,1,0,0,0,1,1,0,0,2,0,2" [left009Row1Part1]

private noncomputable def left009Row1 : List ℕ := left009Row1Part0

private noncomputable def left009Row2Part0 : List ℕ := native_gaps% "0,3,0,1,0,0,6,1,0,0,1,1,0,0,0,1,0,2,2,0,0,2,1,1,0,1,0,0,0,5,1,0,0,1,3,0,0,0,0,0,0,0,0,0,2,0,0,3,0,0,6,9,0,0,2,1,0,2,0,1,1,1,0,3,2,3,1,0,1,1,0,0,5,1,0,0,1,2,2,1,1,0,0,1,2,0,1,0,0,1,3,1,0,1,0,2,3,0,0,1,2,0,2,0,8,1,3,2,2,1" [[]]

private noncomputable def left009Row2 : List ℕ := left009Row2Part0

private noncomputable def left009Row3Part0 : List ℕ := native_gaps% "1,0,0,2,0,0,2,0,0,3,0,4,0,0,3,0,2,0,3,0,0,0,5,0,1,0,3,1,0,1,0,4,0,4,4,0,11,0,0,0,0,1,0,0,2,2,0,0,2,6,0,3,1,1,3,1,0,0,1,5,1,4,1,1,0,0,2,1,1,4,0,0,1,1,1,2,0,5,3,1,0,4,1,3,1,1,0,0,2,2,1,0,0,0,0,0,1,0,0,1,2" [[]]

private noncomputable def left009Row3 : List ℕ := left009Row3Part0

private noncomputable def left009Row4Part0 : List ℕ := native_gaps% "1,1,0,1,0,0,0,0,2,2,0,0,1,6,1,2,1,0,0,0,0,1,1,0,1,1,0,4,1,1,0,1,1,1,0,1,1,6,1,1,0,3,1,0,0,2,1,1,0,1,1,5,1,0,0,1,1,0,2,1,3,1,0,0,3,0,1,0,1,2,0,1,1,0,0,2,1,0,2,0,1,0,1,1,0,0,0,0,2,0,0,2,2,8,1,0,1,6,4,2,1,0,0,0,0,2,1,0,1,1,0,0,2" [[]]

private noncomputable def left009Row4 : List ℕ := left009Row4Part0

private noncomputable def left009Row5Part0 : List ℕ := native_gaps% "1,1,1,0,1,5,2,1,2,5,0,0,0,0,1,1,2,2,2,0,0,1,0,0,1,1,1,0,0,0,5,0,0,2,1,1,0,0,1,0,4,1,3,0,2,0,0,0,2,0,0,0,0,0,0,0,0,1,3,0,0,0,0,3,3,0,0,3,3,1,2,0,0,3,0,0,0,0,0,1,1,0,0,0,1,0,0,1,10,2,1,0,0,0,2,0,0,0,0,0,1,4,0,1,0,0,1,1,1,3,4,0,2,1,2,1" [[]]

private noncomputable def left009Row5 : List ℕ := left009Row5Part0

private noncomputable def left009Row6Part1 : List ℕ := native_gaps% "0" [[]]

private noncomputable def left009Row6Part0 : List ℕ := native_gaps% "0,0,2,3,0,0,4,0,1,1,0,0,0,1,0,0,1,0,5,2,2,0,0,0,0,1,0,0,0,2,1,2,0,3,1,1,0,0,0,2,3,0,0,0,2,0,0,0,1,0,0,2,2,1,0,0,2,0,0,0,1,1,0,0,2,0,3,0,1,4,1,0,0,0,0,0,0,0,1,1,0,1,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,2,1,0,1,1,0,1,2,1,0,1,1,1,1,1,0,7,2,0,0,0,4,1,0,0,3,0,1,4,1,0" [left009Row6Part1]

private noncomputable def left009Row6 : List ℕ := left009Row6Part0

private noncomputable def left009Row7Part0 : List ℕ := native_gaps% "0,3,0,0,0,7,0,1,0,3,0,2,2,2,0,2,0,1,2,1,0,1,1,1,0,0,1,0,2,0,0,1,0,0,0,1,1,0,0,1,0,0,0,1,0,1,3,1,0,2,2,1,1,0,6,0,0,0,0,0,0,3,1,1,1,0,0,3,3,1,0,0,0,1,0,0,0,1,0,0,8,1,0,1,0,0,4,2,0,2,0,0,1,0,1,2,1,1,2,0,0,0,0,0,0,0,0,2,0,0,0,1,1,1,2,2,1,0,2,1,1,1" [[]]

private noncomputable def left009Row7 : List ℕ := left009Row7Part0

private noncomputable def leftGaps009 : List (List ℕ) := [left009Row0, left009Row1, left009Row2, left009Row3, left009Row4, left009Row5, left009Row6, left009Row7]

private noncomputable def right009Row0 : List ℕ := []

private noncomputable def right009Row1 : List ℕ := []

private noncomputable def right009Row2 : List ℕ := []

private noncomputable def right009Row3 : List ℕ := []

private noncomputable def right009Row4 : List ℕ := []

private noncomputable def right009Row5 : List ℕ := []

private noncomputable def right009Row6 : List ℕ := []

private noncomputable def right009Row7 : List ℕ := []

private noncomputable def rightGaps009 : List (List ℕ) := [right009Row0, right009Row1, right009Row2, right009Row3, right009Row4, right009Row5, right009Row6, right009Row7]

private theorem leftMask009 :
    (leftGaps009.map gapMask == (sourceTransposeB.drop 72).take 8) = true := by
  decide +kernel

private theorem rightMask009 :
    (rightGaps009.map gapMask == (quotientTransposeRows.drop 72).take 8) = true := by
  decide +kernel

private theorem products009 :
    (leftGaps009.map (gapRow quotientTransposeRows) == rightGaps009.map (gapRow targetB)) = true := by
  decide +kernel

theorem block009 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 72).take 8) ((quotientTransposeRows.drop 72).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask009) (beq_iff_eq.mp rightMask009)
    (beq_iff_eq.mp products009)

private noncomputable def left010Row0Part0 : List ℕ := native_gaps% "5,0,0,0,0,0,5,2,0,0,0,4,0,2,4,1,3,0,1,0,0,0,1,1,0,0,1,1,2,1,1,2,3,2,0,5,2,0,3,0,2,0,0,0,5,0,0,0,0,2,0,0,0,5,1,0,3,1,0,1,0,0,0,0,0,0,0,2,0,2,4,4,0,2,0,1,1,0,1,0,0,2,1,1,0,0,0,1,0,0,3,1,2,1,2,2,0,0,0,1,1,3,0,1,1,0,0,2,1,4,1,0" [[]]

private noncomputable def left010Row0 : List ℕ := left010Row0Part0

private noncomputable def left010Row1Part0 : List ℕ := native_gaps% "3,1,0,0,2,2,3,0,0,3,1,0,0,7,4,1,0,1,1,0,2,1,0,0,0,0,3,4,1,1,2,0,1,0,0,1,0,0,0,0,2,3,1,0,2,0,1,0,0,1,0,2,2,2,3,4,1,3,1,0,3,0,0,0,3,0,0,2,5,0,1,0,2,0,0,1,0,0,0,0,0,1,0,1,1,0,0,1,1,1,5,1,0,1,0,1,0,0,3,1,0,0,0,2,2,0,1,3,0,0,0,0,0,2" [[]]

private noncomputable def left010Row1 : List ℕ := left010Row1Part0

private noncomputable def left010Row2Part0 : List ℕ := native_gaps% "3,5,0,0,0,0,2,0,0,0,1,1,0,1,0,6,1,0,2,0,3,0,0,6,1,0,3,1,0,1,2,1,1,2,0,0,0,0,1,0,0,0,0,1,0,0,0,0,3,1,0,1,1,0,0,1,1,1,0,1,2,0,1,0,0,0,0,2,0,0,0,1,2,0,2,1,1,2,0,1,0,0,1,0,0,0,2,1,0,0,4,0,0,0,2,2,0,2,2,5,1,3,0,0,0,0,1,4,1,1,1,1,0,0,2,2,0,2" [[]]

private noncomputable def left010Row2 : List ℕ := left010Row2Part0

private noncomputable def left010Row3Part0 : List ℕ := native_gaps% "2,0,2,0,1,1,0,0,2,0,0,5,2,0,2,1,1,0,0,0,0,4,5,0,0,2,0,0,0,1,0,4,0,3,0,0,2,0,0,3,1,0,3,0,1,4,1,0,2,0,1,1,1,0,1,1,1,1,1,2,1,2,2,0,0,1,0,0,2,0,0,0,2,0,3,1,1,6,3,0,0,1,0,0,0,1,3,1,0,1,1,3,3,0,0,0,1,3,1,0,0,0,0,2,1,2,0,1,1,0,1,0,1,1" [[]]

private noncomputable def left010Row3 : List ℕ := left010Row3Part0

private noncomputable def left010Row4Part0 : List ℕ := native_gaps% "1,0,0,1,0,1,1,0,1,0,0,0,0,0,1,2,2,3,2,2,7,3,0,1,0,0,0,1,0,1,1,0,2,0,1,7,0,1,0,0,0,0,1,0,2,4,2,0,0,0,1,0,0,5,1,3,0,1,9,1,0,0,0,2,0,1,0,3,2,0,0,0,1,0,1,0,1,0,0,8,0,1,0,0,3,0,0,4,1,0,0,1,0,0,1,0,3,3,0,1,2,0,0,5,2,1,1,0,0,1,0" [[]]

private noncomputable def left010Row4 : List ℕ := left010Row4Part0

private noncomputable def left010Row5Part0 : List ℕ := native_gaps% "0,0,2,0,1,1,5,0,0,1,0,2,3,1,2,3,1,4,0,0,0,1,3,1,3,0,0,1,1,2,0,0,1,2,0,1,1,0,1,0,2,0,0,1,1,0,2,0,2,2,0,2,0,2,3,0,3,6,1,0,0,1,0,0,1,1,3,3,0,2,1,1,4,0,4,0,1,0,0,1,1,0,2,0,3,4,1,1,0,0,0,0,0,1,0,1,6,0,0,1,0,1,1,0,2,0,1,0,0,0,0,0" [[]]

private noncomputable def left010Row5 : List ℕ := left010Row5Part0

private noncomputable def left010Row6Part0 : List ℕ := native_gaps% "3,0,0,0,0,2,0,1,2,0,1,0,2,0,0,0,0,0,3,0,0,6,1,1,0,2,5,0,0,0,0,3,0,1,1,2,0,0,2,0,1,0,2,8,1,0,1,2,5,1,0,0,4,2,0,0,0,0,1,0,1,3,1,0,2,1,5,1,0,1,2,4,0,3,0,0,1,0,5,3,0,8,0,4,3,0,1,0,1,1,1,0,1,2,1,0,1,0,0,3" [[]]

private noncomputable def left010Row6 : List ℕ := left010Row6Part0

private noncomputable def left010Row7Part0 : List ℕ := native_gaps% "3,1,1,1,0,1,0,0,0,0,1,0,2,1,0,4,1,1,2,0,1,0,0,1,0,0,1,0,0,1,0,3,2,0,0,1,0,0,4,2,1,0,1,1,2,1,6,2,0,0,0,0,1,1,0,3,0,1,4,6,3,2,0,0,1,0,2,0,0,4,0,3,0,1,0,0,0,0,2,4,0,2,0,1,4,1,2,4,0,1,3,0,0,1,0,0,0,0,1,1,2,0,0,3,2,3,0,0,4,0" [[]]

private noncomputable def left010Row7 : List ℕ := left010Row7Part0

private noncomputable def leftGaps010 : List (List ℕ) := [left010Row0, left010Row1, left010Row2, left010Row3, left010Row4, left010Row5, left010Row6, left010Row7]

private noncomputable def right010Row0 : List ℕ := []

private noncomputable def right010Row1 : List ℕ := []

private noncomputable def right010Row2 : List ℕ := []

private noncomputable def right010Row3 : List ℕ := []

private noncomputable def right010Row4 : List ℕ := []

private noncomputable def right010Row5 : List ℕ := []

private noncomputable def right010Row6 : List ℕ := []

private noncomputable def right010Row7 : List ℕ := []

private noncomputable def rightGaps010 : List (List ℕ) := [right010Row0, right010Row1, right010Row2, right010Row3, right010Row4, right010Row5, right010Row6, right010Row7]

private theorem leftMask010 :
    (leftGaps010.map gapMask == (sourceTransposeB.drop 80).take 8) = true := by
  decide +kernel

private theorem rightMask010 :
    (rightGaps010.map gapMask == (quotientTransposeRows.drop 80).take 8) = true := by
  decide +kernel

private theorem products010 :
    (leftGaps010.map (gapRow quotientTransposeRows) == rightGaps010.map (gapRow targetB)) = true := by
  decide +kernel

theorem block010 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 80).take 8) ((quotientTransposeRows.drop 80).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask010) (beq_iff_eq.mp rightMask010)
    (beq_iff_eq.mp products010)

private noncomputable def left011Row0Part0 : List ℕ := native_gaps% "1,0,1,1,1,2,3,2,0,1,0,3,3,1,1,3,0,0,0,0,2,1,1,0,1,0,6,0,0,0,0,0,1,0,1,0,0,0,1,0,0,0,1,0,0,3,1,2,1,1,1,2,0,0,0,2,0,1,6,1,2,0,0,0,0,2,0,1,0,1,0,0,0,2,0,0,0,0,1,0,0,12,0,1,0,0,1,0,0,1,3,1,0,0,0,0,3,0,1,0,1,1,0,1,0,0,2,0,0,0,0,0,2,2,0,0,1,1,2,0,0,0,0,0,0,2" [[]]

private noncomputable def left011Row0 : List ℕ := left011Row0Part0

private noncomputable def left011Row1Part0 : List ℕ := native_gaps% "0,5,0,0,1,0,2,0,1,1,0,4,1,0,1,0,1,2,0,0,0,0,0,0,0,0,0,0,0,1,4,3,0,1,2,2,2,0,0,0,2,1,0,0,0,0,4,2,0,0,0,2,0,0,1,0,1,3,1,0,0,0,1,1,1,1,3,2,1,0,0,3,2,5,0,1,1,0,0,4,0,3,0,1,0,1,3,4,6,1,1,2,0,3,0,1,2,1,4,0,0,2,0,1,3,0,0,1,0,0,0" [[]]

private noncomputable def left011Row1 : List ℕ := left011Row1Part0

private noncomputable def left011Row2Part0 : List ℕ := native_gaps% "4,1,2,0,2,0,0,2,0,0,3,1,4,3,0,0,2,2,5,2,1,0,2,0,0,3,3,0,0,1,0,3,5,1,3,3,6,0,2,0,2,2,0,1,3,6,0,3,0,0,2,5,0,0,0,2,2,1,0,0,0,5,0,0,0,0,0,1,1,2,1,0,0,0,2,2,0,1,0,1,1,1,0,1,0,0,1,1,1,0,2,1,0,4,1,0,0,0,0,1,2,1" [[]]

private noncomputable def left011Row2 : List ℕ := left011Row2Part0

private noncomputable def left011Row3Part0 : List ℕ := native_gaps% "0,1,0,3,1,0,2,1,0,2,2,1,1,0,1,1,1,0,6,0,0,1,1,0,2,0,3,6,0,0,0,0,0,0,5,2,0,0,0,1,0,0,1,1,1,0,0,0,3,0,0,0,6,1,0,0,1,1,0,1,3,5,1,0,0,1,3,1,0,0,1,1,0,0,1,3,1,0,2,2,1,0,3,0,1,0,1,0,0,0,1,2,3,5,0,0,4,0,1,2,1,0,0,0,1,0,0,0,1,1,0,4,0,1" [[]]

private noncomputable def left011Row3 : List ℕ := left011Row3Part0

private noncomputable def left011Row4Part0 : List ℕ := native_gaps% "0,0,2,1,0,2,0,1,0,0,0,3,1,4,0,0,1,0,5,0,0,0,1,0,2,2,0,6,0,1,0,0,0,2,1,1,0,0,1,1,2,0,2,2,0,1,2,3,0,0,0,3,4,2,3,0,1,0,0,0,0,0,0,0,2,1,0,3,1,0,1,3,0,0,2,3,2,0,0,0,0,1,0,1,1,0,1,2,0,1,0,0,0,1,1,1,1,0,2,1,0,0,1,1,0,0,0,1,5,2,0,1,0,0,0,1,5,0,0" [[]]

private noncomputable def left011Row4 : List ℕ := left011Row4Part0

private noncomputable def left011Row5Part0 : List ℕ := native_gaps% "0,0,0,0,1,1,0,0,3,0,0,2,0,0,0,3,4,2,3,1,0,2,0,0,0,3,0,1,0,2,0,0,0,2,2,0,0,0,1,1,1,0,1,0,2,0,0,2,0,1,3,2,0,1,1,0,0,4,0,1,0,0,4,0,0,1,1,0,0,0,7,3,0,0,2,1,4,2,1,0,0,0,1,5,3,0,0,0,0,1,0,1,0,1,3,1,0,3,2,0,0,1,1,3,1,4,1,1,0,0,5,2" [[]]

private noncomputable def left011Row5 : List ℕ := left011Row5Part0

private noncomputable def left011Row6Part0 : List ℕ := native_gaps% "2,0,0,0,3,1,1,0,0,0,2,0,0,2,0,4,3,2,1,2,1,0,0,4,1,0,1,0,3,0,1,0,0,0,1,1,0,1,3,5,0,0,1,6,4,1,1,0,1,2,0,0,1,1,1,0,0,0,0,0,1,1,4,1,0,7,1,1,0,2,1,0,1,0,0,2,0,0,2,4,0,0,2,1,1,0,2,0,0,7,1,3,1,1,0,0,1,0,0,1,0,0,0,0,0,2,1,0,0,0,3,0,0" [[]]

private noncomputable def left011Row6 : List ℕ := left011Row6Part0

private noncomputable def left011Row7Part0 : List ℕ := native_gaps% "4,0,0,1,1,1,0,0,0,0,0,4,0,4,0,0,6,0,0,1,0,2,1,1,4,0,1,0,1,0,0,1,0,0,5,0,0,1,0,1,0,1,0,0,3,1,0,0,0,0,0,0,0,0,0,1,1,6,0,0,1,0,1,0,1,0,2,0,0,4,0,0,0,0,1,0,0,2,1,0,0,0,2,0,0,0,1,0,3,2,2,0,2,3,0,1,3,1,0,1,3,0,0,0,2,0,0,0,1,2,4,1,1,0,0,1,3,0,0,0,1,1,1" [[]]

private noncomputable def left011Row7 : List ℕ := left011Row7Part0

private noncomputable def leftGaps011 : List (List ℕ) := [left011Row0, left011Row1, left011Row2, left011Row3, left011Row4, left011Row5, left011Row6, left011Row7]

private noncomputable def right011Row0 : List ℕ := []

private noncomputable def right011Row1 : List ℕ := []

private noncomputable def right011Row2 : List ℕ := []

private noncomputable def right011Row3 : List ℕ := []

private noncomputable def right011Row4 : List ℕ := []

private noncomputable def right011Row5 : List ℕ := []

private noncomputable def right011Row6 : List ℕ := []

private noncomputable def right011Row7 : List ℕ := []

private noncomputable def rightGaps011 : List (List ℕ) := [right011Row0, right011Row1, right011Row2, right011Row3, right011Row4, right011Row5, right011Row6, right011Row7]

private theorem leftMask011 :
    (leftGaps011.map gapMask == (sourceTransposeB.drop 88).take 8) = true := by
  decide +kernel

private theorem rightMask011 :
    (rightGaps011.map gapMask == (quotientTransposeRows.drop 88).take 8) = true := by
  decide +kernel

private theorem products011 :
    (leftGaps011.map (gapRow quotientTransposeRows) == rightGaps011.map (gapRow targetB)) = true := by
  decide +kernel

theorem block011 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 88).take 8) ((quotientTransposeRows.drop 88).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask011) (beq_iff_eq.mp rightMask011)
    (beq_iff_eq.mp products011)

private noncomputable def left012Row0Part0 : List ℕ := native_gaps% "2,0,0,0,0,1,0,1,0,2,0,1,0,1,0,0,0,0,0,0,5,2,1,1,0,2,6,0,0,1,0,0,1,1,0,0,1,0,1,0,0,0,2,0,0,4,1,1,1,1,2,2,0,0,1,0,0,0,0,0,1,0,0,3,2,0,0,0,0,1,0,6,3,1,4,1,0,0,0,1,0,0,1,1,1,0,1,4,0,0,1,0,0,0,1,2,0,2,0,2,0,1,0,3,0,0,0,2,0,1,2,3,0,0,0,0,1,0,0,2,2,0,1,1,0,0" [[]]

private noncomputable def left012Row0 : List ℕ := left012Row0Part0

private noncomputable def left012Row1Part0 : List ℕ := native_gaps% "0,0,0,1,0,2,2,0,1,2,4,0,1,0,1,0,0,6,2,1,0,0,0,2,0,0,0,2,0,1,0,0,1,1,1,3,1,0,1,1,1,3,0,1,3,0,0,2,1,0,0,3,1,0,1,0,3,0,0,1,2,1,2,1,0,0,2,0,1,1,0,6,3,1,0,0,6,1,1,0,2,0,0,1,0,9,0,2,3,0,1,2,0,0,0,0,1,0,0,0,0,1,2,0,0,0,0,1,1,4,1,0,0" [[]]

private noncomputable def left012Row1 : List ℕ := left012Row1Part0

private noncomputable def left012Row2Part0 : List ℕ := native_gaps% "0,1,0,0,2,2,1,0,0,7,1,1,0,2,1,0,1,0,1,0,1,0,0,1,5,0,0,0,0,0,0,0,0,1,0,0,0,0,2,1,0,0,1,1,0,2,1,0,2,2,1,1,0,1,0,2,1,0,0,0,0,5,0,0,0,2,1,1,0,2,0,0,1,3,1,10,0,0,0,3,1,0,0,1,1,0,1,0,2,0,0,0,1,1,0,0,0,1,0,1,1,2,0,2,1,0,0,0,1,1,0,0,0,0,1,1,1,1,0,3,3,0,1,0,1" [[]]

private noncomputable def left012Row2 : List ℕ := left012Row2Part0

private noncomputable def left012Row3Part0 : List ℕ := native_gaps% "0,0,2,1,3,0,0,2,1,2,0,0,2,3,2,0,0,1,3,4,1,1,1,0,0,1,3,0,5,0,0,0,2,0,0,0,2,1,0,1,2,0,0,0,0,0,1,0,2,0,0,0,1,3,0,0,0,0,0,2,3,0,1,1,0,1,2,0,0,2,0,0,0,2,0,1,1,0,2,0,3,1,2,0,0,1,2,0,2,2,0,2,0,0,0,1,2,2,1,0,0,1,1,0,4,0,0,0,0,1,1,0,5,1,2,0,0,0,2,0,1" [[]]

private noncomputable def left012Row3 : List ℕ := left012Row3Part0

private noncomputable def left012Row4Part0 : List ℕ := native_gaps% "1,5,0,0,0,4,0,2,0,0,0,0,3,0,0,1,2,0,0,1,4,1,1,1,1,0,1,2,1,0,1,0,0,0,4,1,0,0,3,3,7,1,0,1,1,2,0,1,1,1,1,1,1,0,2,0,1,4,3,0,5,0,0,0,0,0,0,0,0,2,3,1,0,0,1,2,0,0,0,6,2,0,1,0,3,1,0,1,0,0,0,0,0,2,2,1,0,0,2,1,1,0,0,0,0,1,0,2,2,4,0,1,0" [[]]

private noncomputable def left012Row4 : List ℕ := left012Row4Part0

private noncomputable def left012Row5Part0 : List ℕ := native_gaps% "0,5,4,0,3,1,0,0,2,0,0,2,0,0,0,0,1,0,1,1,0,3,1,2,4,0,3,1,2,0,2,0,0,1,0,2,4,1,1,0,3,2,1,1,0,8,0,2,0,1,0,2,0,0,0,2,1,3,2,3,0,0,2,0,2,0,2,1,0,0,2,1,0,3,1,2,0,0,2,1,0,0,1,8,0,0,0,0,1,2,3,1,1,3,2,5,0,1,0,2,1" [[]]

private noncomputable def left012Row5 : List ℕ := left012Row5Part0

private noncomputable def left012Row6Part0 : List ℕ := native_gaps% "1,3,4,0,2,0,0,0,0,2,0,2,1,2,0,0,0,0,0,0,0,0,0,2,0,0,0,4,0,1,1,1,3,0,0,3,2,4,0,6,1,2,0,0,0,0,0,0,0,0,0,2,0,2,1,0,7,0,1,2,2,1,1,2,1,0,1,0,0,0,2,0,0,1,0,0,0,2,7,0,1,2,0,0,0,1,0,0,1,0,0,0,1,1,1,0,0,0,2,0,2,1,1,0,0,0,0,0,0,3,1,1,0,2,2,0,0,1,0,5,0" [[]]

private noncomputable def left012Row6 : List ℕ := left012Row6Part0

private noncomputable def left012Row7Part0 : List ℕ := native_gaps% "2,0,1,2,1,1,1,0,0,0,0,0,0,2,1,0,2,0,3,1,0,4,1,0,1,2,0,0,1,0,0,1,0,2,0,0,0,2,1,5,0,2,1,2,0,0,0,0,0,0,0,0,6,0,5,0,0,1,5,1,0,0,0,0,1,0,0,0,0,1,0,0,2,1,1,0,3,2,4,0,4,3,0,0,1,2,0,0,1,3,0,1,1,3,1,0,0,1,0,0,0,0,2,3,1,0,3,1,2,0,2,2,1,0,1,0,0" [[]]

private noncomputable def left012Row7 : List ℕ := left012Row7Part0

private noncomputable def leftGaps012 : List (List ℕ) := [left012Row0, left012Row1, left012Row2, left012Row3, left012Row4, left012Row5, left012Row6, left012Row7]

private noncomputable def right012Row0 : List ℕ := []

private noncomputable def right012Row1 : List ℕ := []

private noncomputable def right012Row2 : List ℕ := []

private noncomputable def right012Row3 : List ℕ := []

private noncomputable def right012Row4 : List ℕ := []

private noncomputable def right012Row5 : List ℕ := []

private noncomputable def right012Row6 : List ℕ := []

private noncomputable def right012Row7 : List ℕ := []

private noncomputable def rightGaps012 : List (List ℕ) := [right012Row0, right012Row1, right012Row2, right012Row3, right012Row4, right012Row5, right012Row6, right012Row7]

private theorem leftMask012 :
    (leftGaps012.map gapMask == (sourceTransposeB.drop 96).take 8) = true := by
  decide +kernel

private theorem rightMask012 :
    (rightGaps012.map gapMask == (quotientTransposeRows.drop 96).take 8) = true := by
  decide +kernel

private theorem products012 :
    (leftGaps012.map (gapRow quotientTransposeRows) == rightGaps012.map (gapRow targetB)) = true := by
  decide +kernel

theorem block012 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 96).take 8) ((quotientTransposeRows.drop 96).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask012) (beq_iff_eq.mp rightMask012)
    (beq_iff_eq.mp products012)

private noncomputable def left013Row0Part0 : List ℕ := native_gaps% "1,5,1,2,0,1,0,0,0,0,1,2,0,0,2,1,0,0,4,0,0,0,3,1,0,0,1,0,6,5,2,4,0,2,0,0,5,0,3,1,1,4,0,3,2,1,0,1,0,0,0,0,2,0,1,4,0,0,1,0,3,0,0,2,0,0,0,1,0,0,1,4,1,0,0,1,0,0,0,0,1,2,0,0,0,1,0,1,3,0,1,0,0,2,0,2,0,0,2,0,0,1,2,0,2,1,4,0,1,1,0,0,1,0,0,0,0,0" [[]]

private noncomputable def left013Row0 : List ℕ := left013Row0Part0

private noncomputable def left013Row1Part0 : List ℕ := native_gaps% "0,0,1,2,0,4,0,2,1,0,0,0,5,3,0,0,2,0,0,0,0,0,0,4,0,2,0,1,4,1,1,0,0,0,0,1,0,0,5,0,1,4,1,0,2,1,0,0,2,0,4,1,0,3,0,2,1,0,3,0,1,1,0,2,1,0,0,0,2,2,2,2,1,1,1,0,2,3,1,1,1,0,0,0,1,0,3,0,0,0,1,4,0,2,4,0,5,1,2,0,0,0,0,0,0,0,0,2,0,1,0,0,1,1,0,0" [[]]

private noncomputable def left013Row1 : List ℕ := left013Row1Part0

private noncomputable def left013Row2Part0 : List ℕ := native_gaps% "0,0,0,3,1,3,0,0,2,2,0,3,1,1,0,2,0,4,4,0,0,0,1,0,1,0,1,0,1,0,1,0,2,0,0,0,0,2,1,0,0,2,2,0,0,1,0,1,1,2,0,1,2,1,2,1,3,0,0,1,3,0,0,0,0,5,0,1,3,3,0,2,0,1,1,1,0,1,0,0,0,0,1,0,3,1,0,1,0,0,0,0,0,0,1,3,0,0,0,0,0,2,0,4,0,0,1,0,3,2,2,2,1,1,1,3,0,0,2,0" [[]]

private noncomputable def left013Row2 : List ℕ := left013Row2Part0

private noncomputable def left013Row3Part0 : List ℕ := native_gaps% "1,0,0,0,0,5,0,1,0,2,3,0,2,2,2,0,0,0,0,0,0,1,2,0,0,3,1,0,0,0,0,8,1,3,0,1,0,0,0,0,0,0,1,0,0,1,0,3,0,1,1,0,4,0,1,0,5,1,1,3,0,0,2,0,0,2,1,0,0,4,0,0,2,3,0,0,0,0,1,1,0,1,1,1,0,1,4,0,2,0,0,0,3,3,4,4,1,0,2,0,3,1,0,1,1,0,0,0,1,0,2,1,0,0,0,0,0,1" [[]]

private noncomputable def left013Row3 : List ℕ := left013Row3Part0

private noncomputable def left013Row4Part0 : List ℕ := native_gaps% "0,0,0,0,1,2,0,0,6,2,0,0,0,2,0,0,1,1,0,1,0,0,0,4,1,4,0,0,2,0,0,0,0,0,1,1,1,3,0,4,0,1,9,0,0,2,0,0,0,2,0,4,4,1,2,1,2,0,4,1,1,0,0,3,0,1,6,2,2,0,0,0,0,4,0,0,1,1,3,0,1,0,0,0,1,5,0,2,2,0,2,1,1,1,0,1,3,0,0,0,0,0,2,2,1,1,0,0,0,0,0,0" [[]]

private noncomputable def left013Row4 : List ℕ := left013Row4Part0

private noncomputable def left013Row5Part0 : List ℕ := native_gaps% "5,0,0,0,0,0,1,2,0,0,1,2,1,0,0,1,0,0,2,2,1,2,1,1,0,1,2,2,0,1,0,3,2,0,2,0,0,0,0,2,0,0,1,1,0,0,2,0,2,0,0,0,1,0,2,1,0,1,0,0,1,1,6,4,3,1,0,0,1,1,0,3,2,1,0,2,1,0,0,0,0,0,0,2,2,2,1,0,3,1,2,3,0,1,0,0,0,0,2,1,0,0,8,0,2,0,0,0,1,2,0,0,2,2,1,0,1" [[]]

private noncomputable def left013Row5 : List ℕ := left013Row5Part0

private noncomputable def left013Row6Part0 : List ℕ := native_gaps% "0,0,0,0,4,0,2,0,2,0,1,1,0,0,2,2,0,0,0,0,3,0,1,0,0,2,5,1,1,0,1,0,0,0,0,5,0,1,0,0,1,0,0,2,0,0,0,1,1,1,3,0,1,0,0,0,1,2,0,4,2,1,0,0,1,4,0,3,4,1,7,0,0,2,1,0,1,0,1,1,2,1,0,0,1,5,0,0,1,1,1,0,3,2,0,3,0,0,0,0,0,3,0,0,0,1,1,0,0,0,0,0,1,2,0,0,0,0,0,0,0,0,0,0" [[]]

private noncomputable def left013Row6 : List ℕ := left013Row6Part0

private noncomputable def left013Row7Part0 : List ℕ := native_gaps% "1,0,1,0,1,1,0,1,0,0,3,0,3,0,0,0,1,0,2,0,3,0,0,2,3,1,0,5,2,0,0,1,2,1,0,0,0,1,0,3,0,0,0,0,1,2,0,1,0,0,12,0,2,1,2,0,0,3,0,0,0,0,4,1,1,4,0,2,0,0,1,0,1,2,0,0,2,2,1,2,0,0,0,1,0,0,0,1,1,0,0,0,0,6,4,0,0,0,1,2,0,6,1,2,0,4,1,0,0,0,2,2" [[]]

private noncomputable def left013Row7 : List ℕ := left013Row7Part0

private noncomputable def leftGaps013 : List (List ℕ) := [left013Row0, left013Row1, left013Row2, left013Row3, left013Row4, left013Row5, left013Row6, left013Row7]

private noncomputable def right013Row0 : List ℕ := []

private noncomputable def right013Row1 : List ℕ := []

private noncomputable def right013Row2 : List ℕ := []

private noncomputable def right013Row3 : List ℕ := []

private noncomputable def right013Row4 : List ℕ := []

private noncomputable def right013Row5 : List ℕ := []

private noncomputable def right013Row6 : List ℕ := []

private noncomputable def right013Row7 : List ℕ := []

private noncomputable def rightGaps013 : List (List ℕ) := [right013Row0, right013Row1, right013Row2, right013Row3, right013Row4, right013Row5, right013Row6, right013Row7]

private theorem leftMask013 :
    (leftGaps013.map gapMask == (sourceTransposeB.drop 104).take 8) = true := by
  decide +kernel

private theorem rightMask013 :
    (rightGaps013.map gapMask == (quotientTransposeRows.drop 104).take 8) = true := by
  decide +kernel

private theorem products013 :
    (leftGaps013.map (gapRow quotientTransposeRows) == rightGaps013.map (gapRow targetB)) = true := by
  decide +kernel

theorem block013 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 104).take 8) ((quotientTransposeRows.drop 104).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask013) (beq_iff_eq.mp rightMask013)
    (beq_iff_eq.mp products013)

private noncomputable def left014Row0Part0 : List ℕ := native_gaps% "1,0,0,0,2,0,2,1,1,1,1,4,1,0,1,0,1,1,0,0,0,1,0,0,4,4,1,1,1,2,0,0,4,0,1,0,0,0,1,0,2,1,0,1,0,0,1,3,0,0,6,0,0,0,3,0,5,0,0,0,1,1,1,2,1,3,0,0,2,4,2,0,2,1,0,2,0,2,1,1,0,0,0,0,0,1,0,5,1,0,0,2,1,0,1,1,2,0,0,0,0,0,1,0,0,0,3,0,2,0,0,1,0,0,1,2,2,0,1" [[]]

private noncomputable def left014Row0 : List ℕ := left014Row0Part0

private noncomputable def left014Row1Part0 : List ℕ := native_gaps% "3,1,3,0,1,0,1,1,1,0,0,0,0,0,3,0,1,0,1,0,0,7,0,1,0,0,4,0,1,1,1,2,0,4,0,1,1,0,1,1,0,0,1,0,0,2,0,2,0,0,1,0,0,3,1,2,1,1,0,1,1,3,2,2,1,1,0,0,3,1,0,2,0,1,4,0,0,0,2,1,0,0,0,0,0,1,1,0,0,0,3,0,1,1,4,0,0,0,0,1,0,0,1,2,3,1,1,0,1,0,1,1,1,0,0,6,3,0" [[]]

private noncomputable def left014Row1 : List ℕ := left014Row1Part0

private noncomputable def left014Row2Part0 : List ℕ := native_gaps% "0,1,2,1,0,0,2,3,0,2,1,0,0,1,0,0,0,3,1,0,3,0,2,4,3,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,1,1,1,0,1,0,1,2,4,0,0,2,0,1,0,4,1,0,0,0,0,0,1,0,0,0,4,0,0,1,0,0,0,4,3,3,6,0,0,3,0,0,1,1,1,0,2,0,0,1,1,4,1,0,0,3,1,0,2,0,2,0,0,2,0,1,0,3,3,2,1,0,0,0,2,0,0,4" [[]]

private noncomputable def left014Row2 : List ℕ := left014Row2Part0

private noncomputable def left014Row3Part0 : List ℕ := native_gaps% "3,0,0,0,0,0,1,0,1,0,1,1,0,0,1,0,2,0,2,1,2,0,0,0,0,0,0,1,2,0,0,0,0,0,0,4,1,0,1,5,0,0,1,1,0,1,0,0,0,2,0,1,1,1,1,1,0,0,5,1,0,0,1,0,0,4,1,0,1,0,3,3,0,2,0,0,2,0,0,0,3,0,0,6,0,1,0,1,0,0,1,0,1,1,0,0,3,0,1,3,1,0,0,0,1,4,2,2,1,4,1,1,0,0,1,0,4,0,2,1,1" [[]]

private noncomputable def left014Row3 : List ℕ := left014Row3Part0

private noncomputable def left014Row4Part0 : List ℕ := native_gaps% "0,1,1,1,0,1,0,0,0,0,0,1,2,1,0,0,1,0,0,0,0,0,1,1,2,1,2,1,3,1,3,1,0,1,5,0,1,1,8,1,1,5,0,0,1,1,3,0,4,0,1,0,0,0,2,0,1,0,2,1,1,0,0,2,0,1,2,0,1,0,0,1,0,0,3,0,1,0,1,0,0,0,2,1,2,0,1,2,0,1,1,1,0,0,4,0,1,2,0,1,0,0,0,2,0,2,0,0,0,3,0,1,0,0,0,2,0,1,0,0,0,0,1" [[]]

private noncomputable def left014Row4 : List ℕ := left014Row4Part0

private noncomputable def left014Row5Part0 : List ℕ := native_gaps% "1,3,1,0,0,4,0,0,1,0,0,1,0,0,3,0,0,1,0,2,1,0,1,0,1,0,0,0,0,1,0,2,0,0,0,0,4,3,0,2,0,0,0,0,2,1,0,0,0,1,0,1,0,0,1,1,4,0,0,0,0,1,1,7,0,0,0,0,2,4,1,0,1,1,0,1,3,0,0,2,0,0,3,0,5,4,0,0,0,0,1,2,3,1,0,2,1,3,4,0,3,0,5,0,0,4,0,0,0,1,0,1,0,2,1,1,0" [[]]

private noncomputable def left014Row5 : List ℕ := left014Row5Part0

private noncomputable def left014Row6Part0 : List ℕ := native_gaps% "1,0,0,0,0,2,4,0,0,0,0,0,0,1,0,0,0,0,0,4,0,1,0,0,3,0,1,0,0,0,1,0,3,0,0,0,4,0,2,1,0,0,4,2,0,3,2,0,3,1,0,0,0,2,1,0,0,0,0,3,0,0,0,2,0,2,1,0,1,5,2,0,0,1,0,0,0,0,1,6,1,0,0,0,4,0,0,0,3,0,0,1,4,5,3,0,1,3,0,4,0,0,1,0,1,0,0,4,0,1,0,0,3,0,0,1,2,1,0" [[]]

private noncomputable def left014Row6 : List ℕ := left014Row6Part0

private noncomputable def left014Row7Part0 : List ℕ := native_gaps% "1,0,0,0,0,0,3,5,0,1,0,0,0,0,1,0,2,3,2,0,0,3,0,0,0,0,1,0,3,4,1,0,0,0,0,3,4,2,0,1,1,1,0,0,3,0,2,0,1,2,0,3,1,1,0,0,0,5,0,1,0,3,1,1,1,1,0,2,3,2,5,1,1,0,0,0,0,0,0,1,0,1,0,1,0,0,0,0,1,0,2,0,3,0,0,0,0,2,0,1,1,1,0,1,1,1,2,4,0,3,1,2,4,0,2" [[]]

private noncomputable def left014Row7 : List ℕ := left014Row7Part0

private noncomputable def leftGaps014 : List (List ℕ) := [left014Row0, left014Row1, left014Row2, left014Row3, left014Row4, left014Row5, left014Row6, left014Row7]

private noncomputable def right014Row0 : List ℕ := []

private noncomputable def right014Row1 : List ℕ := []

private noncomputable def right014Row2 : List ℕ := []

private noncomputable def right014Row3 : List ℕ := []

private noncomputable def right014Row4 : List ℕ := []

private noncomputable def right014Row5 : List ℕ := []

private noncomputable def right014Row6 : List ℕ := []

private noncomputable def right014Row7 : List ℕ := []

private noncomputable def rightGaps014 : List (List ℕ) := [right014Row0, right014Row1, right014Row2, right014Row3, right014Row4, right014Row5, right014Row6, right014Row7]

private theorem leftMask014 :
    (leftGaps014.map gapMask == (sourceTransposeB.drop 112).take 8) = true := by
  decide +kernel

private theorem rightMask014 :
    (rightGaps014.map gapMask == (quotientTransposeRows.drop 112).take 8) = true := by
  decide +kernel

private theorem products014 :
    (leftGaps014.map (gapRow quotientTransposeRows) == rightGaps014.map (gapRow targetB)) = true := by
  decide +kernel

theorem block014 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 112).take 8) ((quotientTransposeRows.drop 112).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask014) (beq_iff_eq.mp rightMask014)
    (beq_iff_eq.mp products014)

private noncomputable def left015Row0Part0 : List ℕ := native_gaps% "2,0,0,2,6,3,0,1,0,0,1,0,0,2,2,0,4,1,0,1,2,2,2,3,0,0,3,0,5,2,0,1,1,0,0,1,1,1,0,0,1,0,1,3,0,0,0,0,1,2,1,1,0,2,0,0,4,0,1,3,1,2,0,4,0,0,2,0,0,0,1,1,1,0,0,1,1,0,0,3,1,0,0,3,0,2,3,1,1,3,0,0,1,0,4,2,0,1,0,1,1,0,1,0,1,1,0,0,0,0,1,0,2,0,0,0" [[]]

private noncomputable def left015Row0 : List ℕ := left015Row0Part0

private noncomputable def left015Row1Part0 : List ℕ := native_gaps% "3,0,1,8,0,0,3,1,1,0,0,1,0,0,0,0,1,0,1,0,1,0,0,1,0,1,1,2,0,1,0,1,0,1,1,4,1,1,5,1,0,0,1,3,2,1,1,0,1,0,0,2,0,1,0,1,0,1,2,1,0,3,0,0,0,0,1,1,2,4,0,1,0,3,3,0,0,4,0,0,0,2,2,0,2,2,0,0,0,2,2,0,5,1,3,0,1,1,0,0,0,2,4,1,1,1,2,6,0,1" [[]]

private noncomputable def left015Row1 : List ℕ := left015Row1Part0

private noncomputable def left015Row2Part0 : List ℕ := native_gaps% "1,0,0,0,0,1,0,0,2,1,3,0,1,0,0,0,0,2,1,0,1,2,0,2,1,1,0,0,0,3,0,0,4,0,0,1,1,3,1,0,1,1,1,0,1,0,2,2,0,0,0,0,0,2,0,0,0,2,0,2,2,7,3,1,0,0,0,0,0,0,2,1,2,1,0,0,1,0,0,0,0,0,1,2,3,0,1,0,3,1,6,2,0,0,0,1,2,0,0,3,2,1,3,0,3,0,0,1,3,1,1,1,1,0,0,1,0,0,2,0" [[]]

private noncomputable def left015Row2 : List ℕ := left015Row2Part0

private noncomputable def left015Row3Part0 : List ℕ := native_gaps% "0,0,4,1,0,2,1,0,3,0,2,5,0,1,0,0,1,0,3,2,2,0,0,1,0,0,1,0,0,2,0,5,0,4,2,3,1,0,0,1,0,0,0,0,1,2,0,10,0,0,0,2,2,2,0,1,0,1,0,2,2,3,1,2,1,0,0,2,0,0,0,0,0,1,0,0,0,2,3,0,3,4,0,0,5,0,0,0,3,0,3,1,1,0,1,4,1,1,0,1,0,2,1,0,0,2,1,0,1" [[]]

private noncomputable def left015Row3 : List ℕ := left015Row3Part0

private noncomputable def left015Row4Part0 : List ℕ := native_gaps% "1,0,1,0,0,1,0,0,4,1,4,0,1,2,1,0,3,1,1,1,1,2,0,1,0,1,3,2,0,1,0,2,1,1,0,2,0,5,1,1,0,0,3,3,1,0,0,0,1,1,2,3,0,1,0,0,4,1,5,0,0,0,0,1,0,3,3,0,0,0,2,0,0,2,1,1,0,0,3,0,1,0,0,3,0,1,1,1,1,0,1,0,0,1,0,0,1,2,3,2,3,0,0,2,1,2,2,2,1,1,2" [[]]

private noncomputable def left015Row4 : List ℕ := left015Row4Part0

private noncomputable def left015Row5Part0 : List ℕ := native_gaps% "0,6,0,1,0,0,2,0,0,1,0,6,1,3,0,2,1,2,2,0,1,1,2,0,0,0,1,1,0,1,0,0,0,0,0,1,2,1,0,0,2,0,1,0,0,0,1,0,2,4,0,0,1,2,0,0,0,0,0,0,3,0,0,4,0,0,0,2,0,1,1,3,3,0,0,1,0,0,0,1,1,2,2,0,0,3,4,2,2,0,3,0,1,1,0,0,2,1,0,0,5,0,6,1,0,0,0,1,0,0,1,1,1,1,1,1,0,0" [[]]

private noncomputable def left015Row5 : List ℕ := left015Row5Part0

private noncomputable def left015Row6Part1 : List ℕ := native_gaps% "5" [[]]

private noncomputable def left015Row6Part0 : List ℕ := native_gaps% "3,1,0,0,1,0,1,1,0,1,0,0,0,2,0,0,3,2,0,1,0,2,0,0,3,0,0,1,0,1,2,1,0,0,0,2,1,0,0,0,1,1,0,0,0,2,2,1,0,0,2,0,0,0,1,2,2,0,0,1,1,0,0,0,1,0,1,2,0,0,1,0,4,0,0,0,0,0,0,1,1,4,0,0,0,2,0,0,1,5,0,2,2,1,3,2,0,0,0,0,0,1,1,2,0,0,0,2,0,0,0,3,1,1,1,1,0,0,0,0,1,0,2,0,1,0,0,1" [left015Row6Part1]

private noncomputable def left015Row6 : List ℕ := left015Row6Part0

private noncomputable def left015Row7Part0 : List ℕ := native_gaps% "1,2,2,0,0,2,4,2,0,0,3,1,0,3,1,1,0,0,0,1,0,2,1,1,2,0,0,0,0,0,0,2,1,0,0,0,0,0,0,2,1,1,7,0,1,0,2,0,0,0,4,1,0,0,3,1,0,0,0,1,4,5,1,0,4,0,0,2,2,2,1,2,1,0,0,1,0,0,0,0,1,1,1,2,1,0,1,0,0,0,1,0,1,3,6,1,1,0,0,1,0,1,0,0,1,1,0,3,2,0,0,1,0,1,0,0,0,2" [[]]

private noncomputable def left015Row7 : List ℕ := left015Row7Part0

private noncomputable def leftGaps015 : List (List ℕ) := [left015Row0, left015Row1, left015Row2, left015Row3, left015Row4, left015Row5, left015Row6, left015Row7]

private noncomputable def right015Row0 : List ℕ := []

private noncomputable def right015Row1 : List ℕ := []

private noncomputable def right015Row2 : List ℕ := []

private noncomputable def right015Row3 : List ℕ := []

private noncomputable def right015Row4 : List ℕ := []

private noncomputable def right015Row5 : List ℕ := []

private noncomputable def right015Row6 : List ℕ := []

private noncomputable def right015Row7 : List ℕ := []

private noncomputable def rightGaps015 : List (List ℕ) := [right015Row0, right015Row1, right015Row2, right015Row3, right015Row4, right015Row5, right015Row6, right015Row7]

private theorem leftMask015 :
    (leftGaps015.map gapMask == (sourceTransposeB.drop 120).take 8) = true := by
  decide +kernel

private theorem rightMask015 :
    (rightGaps015.map gapMask == (quotientTransposeRows.drop 120).take 8) = true := by
  decide +kernel

private theorem products015 :
    (leftGaps015.map (gapRow quotientTransposeRows) == rightGaps015.map (gapRow targetB)) = true := by
  decide +kernel

theorem block015 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 120).take 8) ((quotientTransposeRows.drop 120).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask015) (beq_iff_eq.mp rightMask015)
    (beq_iff_eq.mp products015)

end QuotientGeneratorBChecks
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
