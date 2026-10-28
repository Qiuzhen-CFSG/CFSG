module
public meta import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.GapLiteral
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

private noncomputable def left000Row0Part0 : List ℕ := native_gaps% "2,2,2,6,3,1,0,0,3,0,0,1,1,0,1,4,1,1,1,0,0,1,0,0,7,1,0,0,0,0,0,0,0,1,0,6,5,1,0,0,0,0,0,2,3,0,1,1,3,1,0,0,0,0,1,3,2,2,0,4,0,2,1,0,0,0,0,1,1,0,1,0,2,2,0,1,2,0,2,0,0,0,2,0,2,0,1,1,0,0,1,1,0,4,2,0,0,5,0,1,0,0,4,0,1,0,1,1,3,0" [[]]

private noncomputable def left000Row0 : List ℕ := left000Row0Part0

private noncomputable def left000Row1Part0 : List ℕ := native_gaps% "0,0,0,0,2,0,0,1,0,0,1,0,8,0,1,4,0,0,1,1,1,0,1,1,0,0,2,1,1,1,3,0,1,1,0,0,0,0,0,1,0,0,0,1,2,1,0,0,0,0,0,0,5,0,1,0,0,1,0,0,1,2,0,2,0,0,3,0,1,1,1,3,0,2,0,0,1,0,0,3,0,4,3,9,3,0,1,0,3,1,1,0,0,1,0,2,1,0,1,0,1,0,2,7,0,0,0,0,1,1,0,0,0,0,0,0,1,1,1,0" [[]]

private noncomputable def left000Row1 : List ℕ := left000Row1Part0

private noncomputable def left000Row2Part0 : List ℕ := native_gaps% "0,0,0,0,2,0,0,0,0,0,0,1,2,1,0,2,0,0,0,1,0,0,1,2,0,1,2,0,2,2,1,1,0,1,1,0,2,1,0,0,5,3,0,1,0,0,1,1,0,2,0,0,1,0,0,2,1,0,0,1,4,0,0,0,0,0,2,4,0,0,0,1,1,0,1,3,0,0,3,1,0,0,1,0,0,0,0,3,1,0,1,0,3,1,2,0,3,0,3,0,0,0,1,1,0,6,0,4,0,3,0,0,0,0,0,0,3,0,1,2,1,3,0,1" [[]]

private noncomputable def left000Row2 : List ℕ := left000Row2Part0

private noncomputable def left000Row3Part0 : List ℕ := native_gaps% "2,0,0,0,1,0,2,1,0,0,0,1,0,0,1,3,0,1,0,1,3,1,2,0,0,4,1,0,0,3,0,2,0,4,3,3,0,0,2,0,0,0,0,2,1,2,0,1,4,0,2,0,2,0,1,6,2,2,4,0,1,1,3,0,0,1,0,0,0,0,1,3,4,0,0,3,1,0,5,3,3,0,5,1,2,1,0,4,5,3,1,0,4,0,0,0,6,0,0,0" [[]]

private noncomputable def left000Row3 : List ℕ := left000Row3Part0

private noncomputable def left000Row4Part0 : List ℕ := native_gaps% "0,3,1,0,2,0,2,8,1,1,0,0,0,0,2,1,1,0,1,3,0,1,0,0,0,4,4,0,0,0,1,1,0,0,0,0,0,3,0,0,0,0,0,0,0,1,0,0,2,1,0,0,0,0,1,2,7,1,2,0,0,0,1,0,0,1,1,4,0,0,0,0,1,0,0,0,2,1,0,2,2,0,0,1,1,0,0,1,0,4,9,0,1,0,0,0,1,0,4,0,0,3,0,5,0,1,1,0,1,1,1,1,0,0,0,0" [[]]

private noncomputable def left000Row4 : List ℕ := left000Row4Part0

private noncomputable def left000Row5Part0 : List ℕ := native_gaps% "0,0,0,0,0,0,6,1,2,0,0,1,0,0,0,0,0,3,0,0,3,1,1,1,1,0,0,1,2,0,1,0,0,2,1,0,0,0,0,1,1,2,1,0,0,4,0,6,1,0,0,1,2,1,2,0,2,0,0,0,0,3,0,0,1,1,3,2,0,0,1,1,1,5,2,0,0,0,0,0,2,2,1,4,0,1,1,0,1,0,0,0,1,0,0,1,0,4,2,0,1,0,2,0,0,1,0,1,0,0,3,0,0,0,1,0,0,1,1,0,0,3,0,2" [[]]

private noncomputable def left000Row5 : List ℕ := left000Row5Part0

private noncomputable def left000Row6Part0 : List ℕ := native_gaps% "0,0,1,8,1,0,0,0,0,2,0,3,4,1,1,0,0,1,0,2,0,0,1,3,1,5,3,0,0,3,0,0,0,4,0,0,2,2,1,0,1,2,3,0,0,2,0,0,0,0,1,0,2,1,1,0,1,3,1,1,1,0,0,0,0,0,1,1,0,2,1,2,3,4,3,1,0,0,0,0,2,0,7,0,1,0,2,1,0,0,1,2,0,0,6,0,1,1,1,1,3,0,5,0,3,1,0" [[]]

private noncomputable def left000Row6 : List ℕ := left000Row6Part0

private noncomputable def left000Row7Part0 : List ℕ := native_gaps% "0,1,1,0,4,0,12,1,1,1,1,0,0,0,2,1,0,1,1,3,1,0,0,1,0,0,0,2,1,0,1,0,3,0,1,1,1,0,0,2,1,0,0,1,0,6,1,0,1,0,1,1,1,6,3,0,4,0,1,0,0,0,0,1,4,0,0,1,6,3,0,0,0,0,0,3,0,0,0,1,0,0,1,4,0,2,2,2,0,0,0,6,0,2,1,0,1,1,1,0,0,0,1,1,0,0,0,0,0,0,0,0,0,1" [[]]

private noncomputable def left000Row7 : List ℕ := left000Row7Part0

private noncomputable def leftGaps000 : List (List ℕ) := [left000Row0, left000Row1, left000Row2, left000Row3, left000Row4, left000Row5, left000Row6, left000Row7]

private noncomputable def right000Row0 : List ℕ := []

private noncomputable def right000Row1 : List ℕ := []

private noncomputable def right000Row2 : List ℕ := []

private noncomputable def right000Row3 : List ℕ := []

private noncomputable def right000Row4 : List ℕ := []

private noncomputable def right000Row5 : List ℕ := []

private noncomputable def right000Row6 : List ℕ := []

private noncomputable def right000Row7 : List ℕ := []

private noncomputable def rightGaps000 : List (List ℕ) := [right000Row0, right000Row1, right000Row2, right000Row3, right000Row4, right000Row5, right000Row6, right000Row7]

private theorem leftMask000 :
    (leftGaps000.map gapMask == (sourceTransposeB.drop 0).take 8) = true := by
  decide +kernel

private theorem rightMask000 :
    (rightGaps000.map gapMask == (quotientTransposeRows.drop 0).take 8) = true := by
  decide +kernel

private theorem products000 :
    (leftGaps000.map (gapRow quotientTransposeRows) == rightGaps000.map (gapRow targetB)) = true := by
  decide +kernel

theorem block000 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 0).take 8) ((quotientTransposeRows.drop 0).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask000) (beq_iff_eq.mp rightMask000)
    (beq_iff_eq.mp products000)

private noncomputable def left001Row0Part0 : List ℕ := native_gaps% "5,0,1,2,1,0,0,0,1,1,0,0,1,2,0,0,1,0,0,0,1,4,0,0,0,1,1,0,0,2,2,4,1,0,2,0,3,4,0,1,0,1,2,0,0,1,1,0,1,0,1,0,1,2,0,0,0,0,2,0,0,2,0,1,1,0,6,6,0,6,0,0,1,0,1,1,0,2,0,0,1,0,0,1,0,1,0,0,4,0,0,1,3,1,1,1,1,0,1,4,1,0,0,0,0,1,1,1,0,4,0,0,0,1,0,0,1,1,0,0,0" [[]]

private noncomputable def left001Row0 : List ℕ := left001Row0Part0

private noncomputable def left001Row1Part0 : List ℕ := native_gaps% "0,2,0,3,1,1,1,0,2,0,3,0,0,6,0,1,2,1,0,0,0,4,0,1,2,1,0,4,0,2,0,0,3,1,1,0,0,1,1,0,1,0,1,1,0,6,1,0,0,0,0,0,0,0,3,1,1,4,3,1,1,1,2,6,4,0,2,1,0,0,0,3,2,3,0,3,0,0,0,0,0,0,1,0,2,0,0,0,1,0,1,1,0,3,1,0,1,0,0,2,2,2,1,0,6,0,5" [[]]

private noncomputable def left001Row1 : List ℕ := left001Row1Part0

private noncomputable def left001Row2Part0 : List ℕ := native_gaps% "2,0,4,2,1,0,0,1,3,0,1,0,2,0,0,3,1,0,0,3,0,1,1,0,4,0,1,0,1,0,10,2,0,0,0,1,1,0,1,3,0,0,0,0,1,0,0,0,2,0,2,0,2,7,1,2,2,1,2,0,2,0,1,0,1,1,1,0,4,1,0,3,0,1,0,1,0,2,0,2,3,0,2,0,0,1,5,2,0,7,0,2,0,1,1,0,0,1,1,1,2,1,0,1,0,1,2" [[]]

private noncomputable def left001Row2 : List ℕ := left001Row2Part0

private noncomputable def left001Row3Part0 : List ℕ := native_gaps% "0,0,0,6,2,0,0,0,1,0,0,0,7,2,2,0,0,0,0,0,0,2,0,0,2,3,0,2,2,0,0,1,0,0,0,0,0,1,3,1,2,0,1,3,1,0,0,0,0,0,1,0,0,2,1,0,0,7,0,1,2,0,1,1,3,0,7,0,0,0,0,0,2,3,3,5,1,3,0,1,2,0,1,0,1,1,0,0,0,0,0,0,0,0,0,1,0,0,1,1,0,0,1,2,0,1,0,3,0,0,0,1,2,0,0,6,0,0,1" [[]]

private noncomputable def left001Row3 : List ℕ := left001Row3Part0

private noncomputable def left001Row4Part0 : List ℕ := native_gaps% "1,1,1,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1,3,0,0,0,0,0,1,0,1,0,1,0,0,0,0,5,0,1,1,0,3,1,2,0,0,1,0,1,0,0,2,2,3,1,0,2,0,1,6,1,2,0,1,2,2,0,0,1,0,2,0,0,0,0,0,0,0,1,2,0,1,0,4,0,7,0,2,1,1,0,3,0,0,0,0,0,0,0,0,0,2,0,0,1,1,1,2,0,1,0,0,7,0,0,0,0,0,0,2,1,2,2,0,6" [[]]

private noncomputable def left001Row4 : List ℕ := left001Row4Part0

private noncomputable def left001Row5Part0 : List ℕ := native_gaps% "0,0,1,1,1,1,0,1,6,3,0,0,1,0,2,1,0,4,0,0,0,2,1,0,4,0,3,2,0,0,0,1,5,0,0,2,3,2,0,0,2,3,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,2,0,1,1,0,4,0,0,3,1,0,0,0,3,0,4,4,0,0,0,1,0,0,1,0,0,1,0,6,5,0,0,1,1,0,2,1,0,1,2,1,0,0,2,1,0,0,1,0,0,0,0,1,0,0,1,1,3,0,0,0" [[]]

private noncomputable def left001Row5 : List ℕ := left001Row5Part0

private noncomputable def left001Row6Part0 : List ℕ := native_gaps% "1,0,1,5,0,3,4,2,5,0,0,2,1,0,0,1,4,0,4,1,2,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0,0,1,0,0,1,0,3,0,4,4,0,1,2,1,0,2,8,5,0,1,0,3,2,1,0,1,0,3,1,4,0,0,0,0,0,2,1,1,1,0,1,1,2,1,1,3,0,0,0,1,2,3,0,2,0,2,1,5,2,0,0,2,0,0,1,0,1,0,0,0,0,0" [[]]

private noncomputable def left001Row6 : List ℕ := left001Row6Part0

private noncomputable def left001Row7Part0 : List ℕ := native_gaps% "1,2,0,1,0,1,0,0,2,0,1,1,0,1,0,0,3,0,2,0,2,0,1,4,0,0,0,2,4,3,0,1,0,0,0,0,0,3,0,4,3,0,3,3,0,0,1,0,0,0,0,0,2,4,0,4,0,2,1,0,1,2,0,3,3,0,0,0,2,0,0,0,2,3,1,2,0,4,1,0,0,2,3,1,0,0,0,0,3,0,5,0,1,0,5,1,2,3,1,2,1,0,1,1,2,2,3" [[]]

private noncomputable def left001Row7 : List ℕ := left001Row7Part0

private noncomputable def leftGaps001 : List (List ℕ) := [left001Row0, left001Row1, left001Row2, left001Row3, left001Row4, left001Row5, left001Row6, left001Row7]

private noncomputable def right001Row0 : List ℕ := []

private noncomputable def right001Row1 : List ℕ := []

private noncomputable def right001Row2 : List ℕ := []

private noncomputable def right001Row3 : List ℕ := []

private noncomputable def right001Row4 : List ℕ := []

private noncomputable def right001Row5 : List ℕ := []

private noncomputable def right001Row6 : List ℕ := []

private noncomputable def right001Row7 : List ℕ := []

private noncomputable def rightGaps001 : List (List ℕ) := [right001Row0, right001Row1, right001Row2, right001Row3, right001Row4, right001Row5, right001Row6, right001Row7]

private theorem leftMask001 :
    (leftGaps001.map gapMask == (sourceTransposeB.drop 8).take 8) = true := by
  decide +kernel

private theorem rightMask001 :
    (rightGaps001.map gapMask == (quotientTransposeRows.drop 8).take 8) = true := by
  decide +kernel

private theorem products001 :
    (leftGaps001.map (gapRow quotientTransposeRows) == rightGaps001.map (gapRow targetB)) = true := by
  decide +kernel

theorem block001 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 8).take 8) ((quotientTransposeRows.drop 8).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask001) (beq_iff_eq.mp rightMask001)
    (beq_iff_eq.mp products001)

private noncomputable def left002Row0Part0 : List ℕ := native_gaps% "1,1,2,0,1,0,1,0,1,0,3,2,0,0,0,0,0,1,3,2,2,3,1,1,0,0,1,2,1,0,0,0,0,0,1,1,1,0,1,1,3,0,1,0,1,0,0,0,2,3,1,0,3,0,3,4,3,2,1,1,1,2,1,0,0,5,2,1,3,0,1,1,2,1,1,2,1,2,3,4,1,0,1,0,2,0,2,2,5,2,2,0,6,1,0,0,4,0,0,1,0,0,1,0" [[]]

private noncomputable def left002Row0 : List ℕ := left002Row0Part0

private noncomputable def left002Row1Part0 : List ℕ := native_gaps% "0,3,1,0,1,1,0,0,0,0,3,2,0,0,4,0,0,1,0,0,2,0,0,0,3,3,1,0,1,1,1,0,1,0,0,1,2,0,0,0,2,1,1,0,1,2,0,0,0,0,1,0,0,3,0,2,2,1,0,2,1,0,1,0,2,1,1,2,0,0,1,0,3,3,2,4,0,0,0,0,0,3,2,3,0,2,0,5,1,0,2,0,0,2,1,10,0,0,0,3,1,0,2,7,0,3,0,2,3" [[]]

private noncomputable def left002Row1 : List ℕ := left002Row1Part0

private noncomputable def left002Row2Part0 : List ℕ := native_gaps% "2,2,5,0,0,0,2,1,0,1,2,0,1,3,0,1,3,4,0,2,0,0,0,0,0,7,0,0,0,1,5,1,0,1,0,0,0,0,2,0,2,0,3,3,0,0,0,0,1,0,4,0,0,4,3,0,0,0,1,1,0,0,1,2,0,2,0,3,1,3,2,2,0,1,2,2,1,5,0,0,0,0,3,1,0,1,0,0,2,0,0,0,0,1,3,3,2,0,1,0,0,0,1,2,0,6,1" [[]]

private noncomputable def left002Row2 : List ℕ := left002Row2Part0

private noncomputable def left002Row3Part0 : List ℕ := native_gaps% "2,0,1,0,0,1,0,1,1,0,4,0,0,2,1,0,0,1,0,0,1,0,3,0,3,0,0,1,1,1,1,0,0,0,0,0,2,1,1,0,2,1,3,0,1,0,0,1,1,3,1,0,0,0,7,0,0,0,1,2,5,0,0,0,0,1,1,1,0,0,0,3,2,2,2,2,1,3,1,0,3,1,1,0,4,0,1,1,0,0,1,0,0,0,2,3,0,0,1,0,2,3,4,0,0,3,2,0,1,0,2,1,1,4,0" [[]]

private noncomputable def left002Row3 : List ℕ := left002Row3Part0

private noncomputable def left002Row4Part0 : List ℕ := native_gaps% "0,0,1,0,0,1,4,0,1,2,0,1,1,2,1,0,0,0,0,1,1,0,0,2,4,2,1,7,2,5,2,0,0,0,0,0,0,1,5,0,0,2,0,3,0,3,0,0,1,0,1,3,0,4,4,0,0,0,2,0,0,2,1,3,1,0,0,0,3,1,1,0,0,4,4,1,2,2,1,0,1,0,0,1,0,0,0,0,0,0,0,3,2,0,2,3,1,4,2,0,1,1,0,1,1,0,2,0,0,0,0" [[]]

private noncomputable def left002Row4 : List ℕ := left002Row4Part0

private noncomputable def left002Row5Part0 : List ℕ := native_gaps% "1,0,0,1,0,0,2,2,0,1,0,0,0,3,1,2,0,1,1,0,0,0,2,3,0,0,1,6,1,1,0,3,0,1,0,1,0,2,0,0,0,0,1,0,2,0,1,0,2,0,0,3,1,3,0,0,1,0,1,1,0,0,1,0,0,1,4,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0,1,0,0,0,0,0,0,2,0,0,1,1,3,0,0,1,1,2,3,1,0,0,1,4,0,1,1,2,0,1,1,0,0,1,1,0,5,4,0,0,3,2,0,0,1" [[]]

private noncomputable def left002Row5 : List ℕ := left002Row5Part0

private noncomputable def left002Row6Part0 : List ℕ := native_gaps% "1,2,0,0,2,1,0,0,0,0,0,1,2,0,0,0,0,0,0,0,2,3,2,0,2,0,0,1,0,0,0,1,2,1,2,1,2,2,0,0,3,0,0,0,0,0,2,2,0,2,0,1,0,2,0,1,4,1,4,0,0,0,0,0,1,0,1,0,1,3,4,1,0,0,0,0,0,0,2,1,0,3,0,0,0,1,2,1,1,0,4,1,2,1,0,2,0,2,0,0,0,2,1,1,1,1,0,2,1,3,1,0,4,0,0,2,0,1,3,1,0,0" [[]]

private noncomputable def left002Row6 : List ℕ := left002Row6Part0

private noncomputable def left002Row7Part0 : List ℕ := native_gaps% "1,2,1,0,0,1,0,2,8,1,6,0,1,2,3,0,0,0,0,0,0,0,1,2,0,1,1,0,0,2,0,1,0,0,1,2,1,0,2,1,0,2,1,2,0,2,0,0,0,4,2,0,2,1,0,0,1,0,3,2,0,4,0,0,0,1,2,1,0,3,0,0,0,0,0,0,1,0,0,9,0,0,1,0,1,2,0,1,0,0,0,0,1,0,1,0,0,0,0,1,0,0,0,2,1,0,0,0,2,0,3,1,4,0,1,4,0" [[]]

private noncomputable def left002Row7 : List ℕ := left002Row7Part0

private noncomputable def leftGaps002 : List (List ℕ) := [left002Row0, left002Row1, left002Row2, left002Row3, left002Row4, left002Row5, left002Row6, left002Row7]

private noncomputable def right002Row0 : List ℕ := []

private noncomputable def right002Row1 : List ℕ := []

private noncomputable def right002Row2 : List ℕ := []

private noncomputable def right002Row3 : List ℕ := []

private noncomputable def right002Row4 : List ℕ := []

private noncomputable def right002Row5 : List ℕ := []

private noncomputable def right002Row6 : List ℕ := []

private noncomputable def right002Row7 : List ℕ := []

private noncomputable def rightGaps002 : List (List ℕ) := [right002Row0, right002Row1, right002Row2, right002Row3, right002Row4, right002Row5, right002Row6, right002Row7]

private theorem leftMask002 :
    (leftGaps002.map gapMask == (sourceTransposeB.drop 16).take 8) = true := by
  decide +kernel

private theorem rightMask002 :
    (rightGaps002.map gapMask == (quotientTransposeRows.drop 16).take 8) = true := by
  decide +kernel

private theorem products002 :
    (leftGaps002.map (gapRow quotientTransposeRows) == rightGaps002.map (gapRow targetB)) = true := by
  decide +kernel

theorem block002 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 16).take 8) ((quotientTransposeRows.drop 16).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask002) (beq_iff_eq.mp rightMask002)
    (beq_iff_eq.mp products002)

private noncomputable def left003Row0Part0 : List ℕ := native_gaps% "3,0,6,2,0,1,2,0,0,0,1,1,3,0,0,0,2,1,0,0,2,3,0,0,0,0,1,3,1,0,1,1,4,0,0,1,0,2,0,0,5,0,0,3,0,0,1,2,0,1,0,0,0,3,0,0,2,3,4,0,1,1,2,0,0,0,2,3,0,1,1,0,0,0,2,0,1,1,0,0,1,1,0,0,2,3,2,1,2,0,0,5,1,0,0,6,0,0,1,1,0,0,0,4,0,0,0,0,1,2,2" [[]]

private noncomputable def left003Row0 : List ℕ := left003Row0Part0

private noncomputable def left003Row1Part0 : List ℕ := native_gaps% "0,2,2,0,0,1,0,0,0,0,0,0,3,0,0,1,0,3,1,1,0,1,1,1,1,0,0,1,1,0,2,1,4,1,0,1,0,0,1,4,1,0,1,0,0,0,4,1,1,0,3,0,0,2,1,0,0,0,3,0,4,1,2,2,1,0,0,3,0,0,0,0,1,1,1,0,0,1,2,0,1,1,2,0,0,0,0,1,0,0,0,0,4,4,0,0,1,4,0,0,1,0,1,1,0,6,0,0,0,2,2,3,2,2,2,0,0,0,0,0" [[]]

private noncomputable def left003Row1 : List ℕ := left003Row1Part0

private noncomputable def left003Row2Part0 : List ℕ := native_gaps% "0,3,0,0,1,0,0,1,0,0,0,0,2,0,0,2,0,0,2,0,0,1,0,1,1,2,2,0,0,0,1,0,2,2,0,1,2,2,3,1,1,0,2,2,0,1,0,4,1,3,1,0,1,1,1,0,3,3,1,3,0,0,0,0,0,0,1,2,0,0,0,0,9,3,0,1,0,2,0,1,0,1,2,3,0,1,1,2,1,4,0,3,5,0,0,0,4,0,0,0,1,0,1,0,0,1,2,0,0,0,1,4,0,1,0" [[]]

private noncomputable def left003Row2 : List ℕ := left003Row2Part0

private noncomputable def left003Row3Part0 : List ℕ := native_gaps% "1,0,0,0,1,0,1,0,5,0,1,2,1,1,7,0,0,0,1,0,0,0,0,1,1,0,0,2,0,0,0,1,0,2,0,0,4,1,8,0,0,0,2,3,0,2,0,0,0,0,1,2,2,0,1,0,0,1,1,1,1,2,0,0,1,2,1,0,0,1,0,0,0,2,0,0,0,2,2,0,0,1,1,2,6,1,0,0,0,7,2,3,1,0,0,1,0,0,1,2,0,0,4,2,0,1,0,0,1,0,1,1,1,0,1,1,0,1,0" [[]]

private noncomputable def left003Row3 : List ℕ := left003Row3Part0

private noncomputable def left003Row4Part0 : List ℕ := native_gaps% "3,0,3,0,0,0,0,3,1,0,0,0,2,2,3,1,1,1,2,2,1,0,1,1,0,3,0,0,1,2,0,0,4,0,1,3,0,1,0,0,0,1,0,0,0,0,2,0,1,0,1,0,10,0,0,3,1,1,6,0,2,5,0,1,3,0,3,0,0,0,0,0,0,4,0,0,1,0,1,1,0,3,1,0,0,2,2,4,0,1,1,1,0,1,1,3,1,3,1,0,3,2,0,0,1,0,3" [[]]

private noncomputable def left003Row4 : List ℕ := left003Row4Part0

private noncomputable def left003Row5Part0 : List ℕ := native_gaps% "0,0,0,0,2,0,3,0,0,2,0,1,0,0,3,1,0,1,0,0,1,1,0,1,0,0,0,3,2,2,1,1,0,1,2,0,1,1,0,3,0,3,1,1,0,0,0,5,0,2,1,2,0,0,0,0,0,0,1,0,1,0,0,1,2,1,0,1,0,0,0,0,1,2,1,0,0,2,1,1,0,1,3,1,1,3,1,0,1,0,0,0,4,3,0,0,0,0,0,1,0,3,2,0,5,0,0,0,1,0,2,0,1,0,4,1,1,0,4,1,0,2" [[]]

private noncomputable def left003Row5 : List ℕ := left003Row5Part0

private noncomputable def left003Row6Part0 : List ℕ := native_gaps% "0,0,1,0,0,1,0,0,0,3,0,0,0,1,0,0,4,0,0,1,1,0,1,1,0,1,1,2,1,0,0,0,0,0,1,1,2,1,0,0,0,3,1,1,0,2,1,0,0,3,1,1,2,0,0,0,0,3,9,5,0,2,1,0,0,0,0,1,1,3,0,2,0,0,1,0,1,3,4,0,2,1,0,0,0,0,0,0,0,0,0,2,1,3,0,2,4,1,3,1,0,1,1,0,0,0,0,0,0,0,0,1,2,0,4,0,0,0,0,0,0,1,0,1,0" [[]]

private noncomputable def left003Row6 : List ℕ := left003Row6Part0

private noncomputable def left003Row7Part0 : List ℕ := native_gaps% "0,3,0,0,1,1,0,3,0,1,0,2,4,0,2,0,0,2,0,0,2,1,3,0,0,0,0,1,1,1,0,0,0,3,3,1,1,0,0,0,0,0,2,0,0,0,2,4,0,0,1,0,3,1,4,0,0,0,1,0,0,0,0,1,3,2,0,4,0,0,0,2,4,1,1,0,1,1,0,0,1,0,0,0,1,0,0,1,2,2,0,0,4,0,2,0,4,1,0,0,0,1,0,0,1,0,4,2,0,0,1,8,3,0,1,0,2" [[]]

private noncomputable def left003Row7 : List ℕ := left003Row7Part0

private noncomputable def leftGaps003 : List (List ℕ) := [left003Row0, left003Row1, left003Row2, left003Row3, left003Row4, left003Row5, left003Row6, left003Row7]

private noncomputable def right003Row0 : List ℕ := []

private noncomputable def right003Row1 : List ℕ := []

private noncomputable def right003Row2 : List ℕ := []

private noncomputable def right003Row3 : List ℕ := []

private noncomputable def right003Row4 : List ℕ := []

private noncomputable def right003Row5 : List ℕ := []

private noncomputable def right003Row6 : List ℕ := []

private noncomputable def right003Row7 : List ℕ := []

private noncomputable def rightGaps003 : List (List ℕ) := [right003Row0, right003Row1, right003Row2, right003Row3, right003Row4, right003Row5, right003Row6, right003Row7]

private theorem leftMask003 :
    (leftGaps003.map gapMask == (sourceTransposeB.drop 24).take 8) = true := by
  decide +kernel

private theorem rightMask003 :
    (rightGaps003.map gapMask == (quotientTransposeRows.drop 24).take 8) = true := by
  decide +kernel

private theorem products003 :
    (leftGaps003.map (gapRow quotientTransposeRows) == rightGaps003.map (gapRow targetB)) = true := by
  decide +kernel

theorem block003 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 24).take 8) ((quotientTransposeRows.drop 24).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask003) (beq_iff_eq.mp rightMask003)
    (beq_iff_eq.mp products003)

private noncomputable def left004Row0Part0 : List ℕ := native_gaps% "0,1,0,0,1,0,0,2,0,4,0,0,2,3,2,0,0,0,0,0,3,1,0,0,1,1,1,0,0,1,0,3,2,2,0,1,0,2,1,0,5,3,3,1,0,1,1,1,1,0,0,1,0,0,3,0,0,5,0,1,1,1,1,0,1,2,1,2,5,2,1,0,3,0,4,4,0,1,0,2,2,4,1,2,1,1,1,0,1,4,0,2,0,4,0,0,0,1,0,0,1,0,0,0,1,0,0,2,2,0,0" [[]]

private noncomputable def left004Row0 : List ℕ := left004Row0Part0

private noncomputable def left004Row1Part0 : List ℕ := native_gaps% "0,0,0,1,2,0,0,0,1,2,0,3,1,1,1,0,1,4,0,2,0,0,1,0,0,0,2,3,0,4,4,1,6,0,4,0,7,1,0,2,0,2,0,1,2,2,1,2,1,1,0,1,1,0,2,0,0,4,1,2,0,1,3,3,0,0,2,0,0,0,2,0,0,0,1,0,0,0,0,0,0,1,1,0,1,1,0,2,0,0,2,4,1,0,2,5,0,0,0,0,0,1,0,0,0,1,2,0,0,1,2,0,2,0" [[]]

private noncomputable def left004Row1 : List ℕ := left004Row1Part0

private noncomputable def left004Row2Part0 : List ℕ := native_gaps% "1,0,1,5,0,1,1,0,1,5,4,1,3,0,0,3,0,0,1,1,0,1,0,2,0,0,1,0,0,0,5,0,2,1,0,1,0,1,0,0,2,0,2,3,2,2,7,0,0,0,3,0,2,4,0,0,2,2,0,0,1,3,0,1,0,0,0,1,4,0,0,0,0,0,0,3,1,0,0,1,1,0,0,4,0,0,0,1,1,0,1,0,1,0,2,0,0,0,4,1,0,1,0,0,0,2,0,5,0,5,0,1,0" [[]]

private noncomputable def left004Row2 : List ℕ := left004Row2Part0

private noncomputable def left004Row3Part0 : List ℕ := native_gaps% "7,0,0,2,0,0,0,0,1,0,0,0,0,0,0,2,0,0,3,2,0,2,3,4,1,4,3,0,0,1,1,1,0,2,0,2,1,3,1,1,1,2,1,1,3,0,4,0,1,0,1,3,0,1,1,2,0,1,0,0,1,1,1,3,0,1,2,0,0,0,1,3,0,5,1,0,3,3,0,4,0,0,0,0,1,0,1,1,1,0,2,0,1,0,0,1,1,0,2,0,4,1,0,2,2,0,6,0" [[]]

private noncomputable def left004Row3 : List ℕ := left004Row3Part0

private noncomputable def left004Row4Part0 : List ℕ := native_gaps% "0,0,0,1,0,0,2,0,0,0,2,0,0,2,0,1,2,6,0,2,2,1,0,0,0,0,0,0,1,0,4,0,0,3,1,5,0,4,2,0,0,0,0,0,2,1,0,0,0,2,0,3,0,2,0,0,0,0,0,0,2,4,0,0,3,1,1,3,0,0,0,1,1,2,2,0,0,0,2,1,1,0,2,0,0,7,0,0,3,0,0,0,0,1,0,2,2,3,0,1,0,1,2,0,0,1,1,1,2,0,0,0,1,0,0,0,2,0,6" [[]]

private noncomputable def left004Row4 : List ℕ := left004Row4Part0

private noncomputable def left004Row5Part0 : List ℕ := native_gaps% "0,0,0,0,0,0,1,1,0,0,0,0,1,2,7,0,0,2,1,0,2,2,0,2,0,1,0,0,0,6,1,1,4,1,0,0,2,2,0,0,0,5,0,0,0,0,1,2,0,1,1,0,0,1,1,1,0,3,1,4,0,0,0,1,2,0,1,0,0,0,2,1,1,1,1,1,1,0,0,0,0,1,1,2,1,0,4,3,0,0,2,1,1,4,5,3,0,0,0,1,0,0,2,1,3,2,0,1,2,0,0,2,2,1,0" [[]]

private noncomputable def left004Row5 : List ℕ := left004Row5Part0

private noncomputable def left004Row6Part1 : List ℕ := native_gaps% "1,1,0,1,1,0,0" [[]]

private noncomputable def left004Row6Part0 : List ℕ := native_gaps% "3,1,0,0,0,1,3,0,0,0,1,2,0,1,0,2,2,1,0,0,0,0,4,0,0,1,1,1,0,0,0,0,2,2,1,1,3,0,2,3,1,1,0,0,0,1,1,0,2,0,0,1,0,0,0,0,0,0,0,0,0,0,4,1,0,2,1,0,0,0,0,0,1,0,1,0,0,0,0,1,0,0,0,0,2,0,0,1,2,1,0,0,0,0,0,1,0,1,0,1,0,0,0,0,1,1,1,3,2,0,1,3,0,0,1,2,1,1,3,0,2,1,1,1,0,1,1,0" [left004Row6Part1]

private noncomputable def left004Row6 : List ℕ := left004Row6Part0

private noncomputable def left004Row7Part0 : List ℕ := native_gaps% "0,3,1,0,1,6,1,0,1,0,0,1,0,1,1,4,2,0,0,0,3,2,3,0,1,0,0,0,1,1,1,0,0,1,0,1,0,0,0,3,1,2,1,0,3,2,1,2,1,2,2,0,4,6,2,3,0,0,1,0,1,0,1,4,1,0,3,7,0,1,0,1,0,1,0,1,1,1,1,1,7,1,0,1,1,1,0,0,1,0,0,0,0,0,6,3,4,2,0,4,0,0,0,0" [[]]

private noncomputable def left004Row7 : List ℕ := left004Row7Part0

private noncomputable def leftGaps004 : List (List ℕ) := [left004Row0, left004Row1, left004Row2, left004Row3, left004Row4, left004Row5, left004Row6, left004Row7]

private noncomputable def right004Row0 : List ℕ := []

private noncomputable def right004Row1 : List ℕ := []

private noncomputable def right004Row2 : List ℕ := []

private noncomputable def right004Row3 : List ℕ := []

private noncomputable def right004Row4 : List ℕ := []

private noncomputable def right004Row5 : List ℕ := []

private noncomputable def right004Row6 : List ℕ := []

private noncomputable def right004Row7 : List ℕ := []

private noncomputable def rightGaps004 : List (List ℕ) := [right004Row0, right004Row1, right004Row2, right004Row3, right004Row4, right004Row5, right004Row6, right004Row7]

private theorem leftMask004 :
    (leftGaps004.map gapMask == (sourceTransposeB.drop 32).take 8) = true := by
  decide +kernel

private theorem rightMask004 :
    (rightGaps004.map gapMask == (quotientTransposeRows.drop 32).take 8) = true := by
  decide +kernel

private theorem products004 :
    (leftGaps004.map (gapRow quotientTransposeRows) == rightGaps004.map (gapRow targetB)) = true := by
  decide +kernel

theorem block004 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 32).take 8) ((quotientTransposeRows.drop 32).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask004) (beq_iff_eq.mp rightMask004)
    (beq_iff_eq.mp products004)

private noncomputable def left005Row0Part0 : List ℕ := native_gaps% "1,0,1,3,4,0,2,0,1,2,3,0,2,0,0,0,0,1,1,2,0,0,2,1,1,0,0,1,5,0,0,0,0,0,4,0,12,2,0,0,0,0,1,0,1,0,0,0,5,1,1,0,0,1,0,3,0,0,4,1,0,3,1,0,0,1,1,0,1,1,1,1,0,3,1,1,0,0,0,3,0,0,1,0,2,2,1,0,3,0,4,3,0,0,3,0,0,5,2,0,3,0,0,0,2,0,4,0,0" [[]]

private noncomputable def left005Row0 : List ℕ := left005Row0Part0

private noncomputable def left005Row1Part0 : List ℕ := native_gaps% "2,0,0,0,1,1,1,1,1,0,0,0,2,0,1,1,0,6,1,0,0,0,0,1,0,3,1,0,0,1,0,0,0,7,0,1,0,1,0,0,0,1,1,0,0,1,0,3,0,0,1,0,1,1,1,4,1,0,1,0,0,0,0,0,0,0,0,3,0,5,0,2,0,0,3,0,0,1,1,0,3,5,5,1,3,1,0,0,0,0,0,0,1,2,0,1,4,0,1,1,1,0,1,0,2,1,1,0,1,3,0,0,0,2,1,4,1,2" [[]]

private noncomputable def left005Row1 : List ℕ := left005Row1Part0

private noncomputable def left005Row2Part0 : List ℕ := native_gaps% "2,1,5,1,0,0,2,0,5,1,0,0,3,3,0,1,0,1,0,1,1,0,0,0,0,1,1,2,0,1,4,0,0,0,0,0,0,3,0,2,0,1,3,1,2,0,2,1,0,0,0,1,2,3,1,0,0,0,1,0,1,0,3,0,0,0,0,0,3,0,2,1,2,0,1,0,0,0,1,2,1,1,0,6,0,1,0,2,1,0,4,0,1,0,0,3,3,0,0,0,1,1,0,2,1,2,2,0,1,2,0,1,3,0,0" [[]]

private noncomputable def left005Row2 : List ℕ := left005Row2Part0

private noncomputable def left005Row3Part0 : List ℕ := native_gaps% "0,2,2,2,0,3,1,1,3,0,0,4,0,0,0,0,1,2,0,0,2,1,1,0,0,2,0,3,0,0,0,2,1,3,2,2,0,0,4,1,0,0,0,0,1,0,2,1,0,1,2,0,0,0,1,0,0,1,3,1,0,0,0,3,0,0,3,2,4,1,0,0,0,0,3,0,0,4,0,0,1,2,1,0,0,2,3,0,0,2,1,0,0,2,3,2,0,0,0,6,0,2,0,0,0,0,2,3,3,1,0,0,0,0,3" [[]]

private noncomputable def left005Row3 : List ℕ := left005Row3Part0

private noncomputable def left005Row4Part0 : List ℕ := native_gaps% "1,1,3,3,0,2,0,0,0,1,0,0,0,0,2,0,1,0,4,0,1,0,2,3,0,0,2,1,1,4,0,1,1,1,0,1,0,1,0,2,1,0,0,1,0,1,1,0,0,0,1,0,0,6,1,0,2,1,0,2,0,1,0,3,0,1,2,1,0,0,0,4,1,1,2,0,0,1,2,0,0,0,0,0,1,0,0,0,1,1,0,1,0,2,0,1,1,1,0,1,0,3,0,1,1,2,0,0,2,0,1,0,0,1,1,4,0,1,1,1,2,1,1,0" [[]]

private noncomputable def left005Row4 : List ℕ := left005Row4Part0

private noncomputable def left005Row5Part0 : List ℕ := native_gaps% "1,0,1,0,1,0,3,1,0,0,3,0,0,0,0,0,0,0,0,1,1,0,1,2,0,0,2,0,2,2,0,0,6,0,0,1,0,0,0,1,0,0,3,1,0,0,0,1,2,0,3,0,0,2,0,0,0,5,3,0,0,2,0,0,3,0,2,0,2,0,1,1,0,5,1,0,1,0,1,0,3,1,0,0,5,0,0,2,0,1,0,1,2,1,0,0,2,1,1,0,1,0,3,1,0,1,0,0,5,5,4,2,1,0,2,0" [[]]

private noncomputable def left005Row5 : List ℕ := left005Row5Part0

private noncomputable def left005Row6Part0 : List ℕ := native_gaps% "0,1,0,0,0,1,1,0,0,1,0,3,2,1,5,2,0,3,0,0,1,0,1,0,0,1,0,0,2,0,4,0,0,0,0,1,1,0,0,1,2,3,2,2,4,2,0,0,0,0,2,2,1,1,0,2,3,0,0,0,0,1,1,4,0,3,1,1,1,0,0,1,0,0,1,0,0,1,0,0,0,0,0,1,0,0,3,0,6,0,1,0,1,1,0,1,1,1,5,1,1,1,0,0,2,0,1,1,0,0,1,0,0,3,0,0,3,0,1,1,1" [[]]

private noncomputable def left005Row6 : List ℕ := left005Row6Part0

private noncomputable def left005Row7Part0 : List ℕ := native_gaps% "0,1,2,1,1,0,0,1,0,1,1,2,2,0,1,1,1,0,3,0,0,0,1,5,2,1,0,2,0,1,1,0,1,1,0,0,0,4,2,1,1,0,0,0,1,0,2,2,0,0,1,1,0,1,1,2,1,0,1,1,0,0,1,0,0,1,3,4,0,0,1,0,2,0,1,1,1,0,1,2,0,1,0,4,3,0,0,0,2,0,1,1,0,1,0,1,3,0,1,0,0,2,1,0,0,4,1,0,1,6,1,1,0,5,2" [[]]

private noncomputable def left005Row7 : List ℕ := left005Row7Part0

private noncomputable def leftGaps005 : List (List ℕ) := [left005Row0, left005Row1, left005Row2, left005Row3, left005Row4, left005Row5, left005Row6, left005Row7]

private noncomputable def right005Row0 : List ℕ := []

private noncomputable def right005Row1 : List ℕ := []

private noncomputable def right005Row2 : List ℕ := []

private noncomputable def right005Row3 : List ℕ := []

private noncomputable def right005Row4 : List ℕ := []

private noncomputable def right005Row5 : List ℕ := []

private noncomputable def right005Row6 : List ℕ := []

private noncomputable def right005Row7 : List ℕ := []

private noncomputable def rightGaps005 : List (List ℕ) := [right005Row0, right005Row1, right005Row2, right005Row3, right005Row4, right005Row5, right005Row6, right005Row7]

private theorem leftMask005 :
    (leftGaps005.map gapMask == (sourceTransposeB.drop 40).take 8) = true := by
  decide +kernel

private theorem rightMask005 :
    (rightGaps005.map gapMask == (quotientTransposeRows.drop 40).take 8) = true := by
  decide +kernel

private theorem products005 :
    (leftGaps005.map (gapRow quotientTransposeRows) == rightGaps005.map (gapRow targetB)) = true := by
  decide +kernel

theorem block005 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 40).take 8) ((quotientTransposeRows.drop 40).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask005) (beq_iff_eq.mp rightMask005)
    (beq_iff_eq.mp products005)

private noncomputable def left006Row0Part0 : List ℕ := native_gaps% "0,2,4,0,1,0,0,0,0,1,0,0,0,1,3,0,0,3,3,0,0,0,0,0,0,0,1,0,7,1,0,0,0,1,1,0,0,0,1,2,0,1,0,1,1,0,0,0,0,0,2,2,2,3,3,0,0,0,2,1,2,0,0,2,1,1,0,1,1,0,1,0,0,2,2,1,2,0,0,0,0,0,0,1,1,2,0,1,0,1,0,0,1,0,2,0,1,1,2,4,1,0,0,0,0,2,0,6,0,1,0,0,2,1,0,1,0,0,0,0,1,1,2,0,1,3,0" [[]]

private noncomputable def left006Row0 : List ℕ := left006Row0Part0

private noncomputable def left006Row1Part1 : List ℕ := native_gaps% "0" [[]]

private noncomputable def left006Row1Part0 : List ℕ := native_gaps% "0,2,0,0,0,0,0,1,1,1,0,0,1,0,0,1,0,0,2,0,1,0,1,0,0,1,0,0,0,1,1,3,0,0,0,1,0,0,1,0,0,0,0,0,0,0,1,4,0,1,0,1,6,0,1,1,0,2,0,1,0,4,1,0,0,1,2,3,0,1,0,1,0,1,1,0,2,0,0,0,0,2,0,0,0,3,1,0,2,0,1,3,0,4,1,0,2,0,6,0,1,0,4,0,1,1,0,0,1,0,1,0,0,1,0,1,1,2,1,2,0,1,0,2,0,3,0,1" [left006Row1Part1]

private noncomputable def left006Row1 : List ℕ := left006Row1Part0

private noncomputable def left006Row2Part0 : List ℕ := native_gaps% "0,0,0,0,0,0,0,0,0,0,2,3,1,0,0,1,0,0,0,2,0,0,2,0,2,0,0,2,3,4,1,0,0,0,0,1,0,0,0,0,0,4,1,0,0,2,1,0,0,0,0,0,0,0,2,1,2,1,1,1,1,3,1,0,1,0,2,0,0,0,2,0,1,0,0,0,3,2,1,0,1,0,2,0,0,0,1,0,2,0,1,0,0,0,4,2,6,1,0,0,1,5,0,3,1,0,1,0,0,3,0,1,0,1,0,1,0,1,1,1,5,0,0,1,0,0" [[]]

private noncomputable def left006Row2 : List ℕ := left006Row2Part0

private noncomputable def left006Row3Part0 : List ℕ := native_gaps% "0,2,0,0,0,1,0,3,1,1,1,1,1,0,2,0,0,2,3,0,2,1,1,0,0,0,0,0,0,2,0,3,0,0,1,2,3,0,1,0,2,2,0,1,0,0,1,1,0,5,0,0,3,1,0,4,0,2,2,0,0,0,1,0,0,5,1,1,0,1,2,1,1,1,1,1,0,4,0,0,4,0,1,2,0,0,0,0,0,5,0,3,1,0,0,2,0,0,0,2,0,0,0,1,2,0,3,0,2,0,0,0,0,1,0,2,0,0,0,0,0,1" [[]]

private noncomputable def left006Row3 : List ℕ := left006Row3Part0

private noncomputable def left006Row4Part0 : List ℕ := native_gaps% "0,0,3,0,5,1,0,0,2,4,3,1,0,0,0,3,1,4,0,1,0,0,1,1,1,0,1,1,0,0,0,0,2,0,0,2,0,1,0,0,1,0,2,0,3,0,2,0,1,0,1,3,0,2,2,4,0,0,0,0,1,0,0,0,0,0,0,6,0,0,1,2,1,0,0,0,0,0,3,0,0,0,1,1,1,0,0,1,0,0,0,0,0,0,0,0,0,3,2,0,0,0,3,0,1,3,0,0,0,2,3,3,1,1,0,1,0,0,0,0,0,1,0,0,4" [[]]

private noncomputable def left006Row4 : List ℕ := left006Row4Part0

private noncomputable def left006Row5Part0 : List ℕ := native_gaps% "3,0,2,0,1,0,0,0,1,0,0,0,0,1,2,0,2,0,0,0,3,0,4,0,0,2,1,2,0,0,0,5,2,0,0,3,0,0,0,3,0,0,0,0,2,1,1,1,1,3,0,1,0,0,0,0,3,0,1,0,0,5,0,0,0,0,0,0,1,2,0,0,0,0,0,0,3,0,0,2,0,2,1,0,0,0,0,1,0,0,1,1,0,0,0,1,0,1,2,4,1,4,1,0,3,9,2,0,0,1,0,2,0,2,1,1,2,0,1,1,0,0,0" [[]]

private noncomputable def left006Row5 : List ℕ := left006Row5Part0

private noncomputable def left006Row6Part0 : List ℕ := native_gaps% "3,0,3,2,2,0,2,0,2,7,1,0,3,3,0,2,0,7,2,1,0,3,0,1,2,3,0,0,0,0,0,0,0,1,0,2,1,4,2,0,0,1,0,1,1,0,0,1,0,0,1,0,1,2,0,0,0,3,0,0,0,0,2,0,1,0,0,2,1,0,0,1,0,0,1,0,1,4,0,2,0,1,2,1,0,3,1,0,2,2,0,0,0,5,1,0,0,0,0,0,1,1,1,0,0,0,0,1,2,3,0,1,0,1,0,1,0" [[]]

private noncomputable def left006Row6 : List ℕ := left006Row6Part0

private noncomputable def left006Row7Part0 : List ℕ := native_gaps% "4,0,2,1,2,2,0,0,4,5,0,2,3,1,3,1,0,1,1,0,1,1,0,1,2,1,3,0,0,0,1,2,0,0,1,0,2,0,3,0,0,0,0,2,0,0,0,0,3,0,1,1,0,1,2,0,0,1,1,4,0,0,1,0,0,0,0,0,0,2,0,0,3,0,0,0,0,0,2,1,0,1,0,0,0,2,0,1,0,0,1,0,0,0,1,1,10,0,0,0,0,0,1,2,2,2,0,2,0,0,1,0,3,0,4,3,0,1,0" [[]]

private noncomputable def left006Row7 : List ℕ := left006Row7Part0

private noncomputable def leftGaps006 : List (List ℕ) := [left006Row0, left006Row1, left006Row2, left006Row3, left006Row4, left006Row5, left006Row6, left006Row7]

private noncomputable def right006Row0 : List ℕ := []

private noncomputable def right006Row1 : List ℕ := []

private noncomputable def right006Row2 : List ℕ := []

private noncomputable def right006Row3 : List ℕ := []

private noncomputable def right006Row4 : List ℕ := []

private noncomputable def right006Row5 : List ℕ := []

private noncomputable def right006Row6 : List ℕ := []

private noncomputable def right006Row7 : List ℕ := []

private noncomputable def rightGaps006 : List (List ℕ) := [right006Row0, right006Row1, right006Row2, right006Row3, right006Row4, right006Row5, right006Row6, right006Row7]

private theorem leftMask006 :
    (leftGaps006.map gapMask == (sourceTransposeB.drop 48).take 8) = true := by
  decide +kernel

private theorem rightMask006 :
    (rightGaps006.map gapMask == (quotientTransposeRows.drop 48).take 8) = true := by
  decide +kernel

private theorem products006 :
    (leftGaps006.map (gapRow quotientTransposeRows) == rightGaps006.map (gapRow targetB)) = true := by
  decide +kernel

theorem block006 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 48).take 8) ((quotientTransposeRows.drop 48).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask006) (beq_iff_eq.mp rightMask006)
    (beq_iff_eq.mp products006)

private noncomputable def left007Row0Part0 : List ℕ := native_gaps% "0,0,0,0,0,0,1,0,1,1,4,4,5,1,0,1,4,0,0,0,0,4,2,0,3,2,0,0,0,1,1,1,1,2,1,0,1,1,0,2,1,0,0,1,0,0,0,1,0,2,1,2,0,0,5,3,0,3,0,1,1,1,1,2,0,0,0,1,4,1,1,1,1,1,2,4,0,7,0,0,1,3,3,0,0,0,3,2,0,0,0,0,4,0,1,0,1,0,1,0,2,1,0,0,0,4,1,0,1,1,0" [[]]

private noncomputable def left007Row0 : List ℕ := left007Row0Part0

private noncomputable def left007Row1Part0 : List ℕ := native_gaps% "0,0,0,1,1,2,3,2,3,0,0,1,0,0,1,0,1,1,0,1,0,2,0,0,3,0,4,2,1,2,0,1,0,0,0,0,0,0,0,0,0,1,3,2,0,1,0,2,0,1,0,2,0,0,0,1,1,0,2,3,1,1,2,1,1,4,2,0,0,0,1,3,3,3,0,2,0,0,2,0,0,2,0,3,0,1,1,0,2,0,0,2,0,0,0,1,0,2,2,1,0,0,0,0,0,2,0,0,3,0,0,0,4,1,0,1,0,0,0,0,1,2,1" [[]]

private noncomputable def left007Row1 : List ℕ := left007Row1Part0

private noncomputable def left007Row2Part0 : List ℕ := native_gaps% "0,0,1,0,1,2,0,3,2,0,1,2,0,0,1,2,1,5,3,2,0,0,1,1,5,2,1,5,1,0,2,0,0,3,0,1,1,1,0,2,0,0,0,0,2,6,0,0,2,1,1,0,0,0,0,1,0,1,0,2,0,4,0,0,1,1,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,1,0,1,0,0,0,1,2,0,1,0,2,0,0,0,1,0,1,2,0,1,0,0,0,2,0,6,1,0,0,1,1,0,1,1,0,0,1,0,0,0,0,0,0,0" [[]]

private noncomputable def left007Row2 : List ℕ := left007Row2Part0

private noncomputable def left007Row3Part0 : List ℕ := native_gaps% "0,3,3,0,4,0,2,0,0,0,4,3,1,0,0,1,0,1,1,1,1,3,0,0,2,0,1,0,0,1,0,2,1,1,0,0,1,0,0,1,1,1,2,1,6,0,0,0,0,2,4,0,1,3,0,1,0,1,2,0,1,0,1,2,1,0,2,0,0,0,6,0,1,0,1,0,4,1,0,0,0,0,0,1,1,1,0,1,0,1,0,1,0,3,0,0,0,0,0,0,2,0,2,0,1,3,1,1,1,0,0,1,3,2,0,0,1,0,1,1" [[]]

private noncomputable def left007Row3 : List ℕ := left007Row3Part0

private noncomputable def left007Row4Part0 : List ℕ := native_gaps% "0,3,1,1,0,2,2,0,1,5,2,0,0,2,0,0,1,0,0,0,0,1,3,1,0,8,1,0,6,2,1,0,0,1,0,2,1,2,0,2,2,2,0,0,0,1,0,0,4,4,0,0,0,0,0,0,1,0,1,0,0,3,2,0,1,2,0,0,2,0,0,3,2,1,0,1,0,0,1,2,0,2,2,0,0,1,2,2,0,3,0,5,2,0,0,3,0,0,0,0,1,0,0,0,2,0,0,0,1,1,0,0,1,2" [[]]

private noncomputable def left007Row4 : List ℕ := left007Row4Part0

private noncomputable def left007Row5Part0 : List ℕ := native_gaps% "2,4,0,1,1,0,0,1,0,1,0,0,0,1,2,0,0,0,0,0,1,2,1,0,1,2,0,0,0,1,1,0,1,1,3,2,0,1,0,0,0,2,1,1,1,1,1,1,3,1,0,0,5,0,1,0,0,2,2,2,2,2,0,1,0,2,1,0,0,0,2,1,1,2,0,0,1,1,1,4,0,1,2,2,0,1,0,1,1,1,0,1,1,2,0,0,1,0,1,1,1,0,0,0,0,0,1,1,0,1,0,0,0,0,0,1,0,0,1,3,1,0,2,0,0,0,1,0" [[]]

private noncomputable def left007Row5 : List ℕ := left007Row5Part0

private noncomputable def left007Row6Part0 : List ℕ := native_gaps% "0,4,1,1,0,0,1,7,0,2,1,1,1,1,0,0,0,1,2,0,0,0,0,1,0,0,0,0,1,5,1,1,0,0,1,0,2,3,0,1,2,1,1,0,1,0,1,1,1,0,0,1,0,0,0,4,1,1,0,0,0,1,2,3,1,2,0,1,0,2,2,1,0,0,1,0,0,0,0,0,1,0,0,1,1,0,2,2,0,2,0,0,1,3,4,1,3,1,2,2,1,1,2,0,1,2,1,0,4,1,0,0,0,1,1,2,0,1" [[]]

private noncomputable def left007Row6 : List ℕ := left007Row6Part0

private noncomputable def left007Row7Part0 : List ℕ := native_gaps% "0,0,0,0,0,0,0,5,0,0,0,0,3,1,2,2,0,0,0,0,0,0,1,2,2,3,1,0,1,0,1,0,2,2,0,0,0,0,2,1,0,1,0,0,4,0,3,0,0,0,0,5,0,0,0,1,0,2,0,0,0,1,0,6,0,0,3,0,0,2,0,0,0,0,2,0,2,0,0,2,0,3,1,2,2,0,4,0,7,0,5,4,2,2,0,2,2,1,1,1,0,2,0,0,0,1,1,1,2,1,0,2,0,1,1,0" [[]]

private noncomputable def left007Row7 : List ℕ := left007Row7Part0

private noncomputable def leftGaps007 : List (List ℕ) := [left007Row0, left007Row1, left007Row2, left007Row3, left007Row4, left007Row5, left007Row6, left007Row7]

private noncomputable def right007Row0 : List ℕ := []

private noncomputable def right007Row1 : List ℕ := []

private noncomputable def right007Row2 : List ℕ := []

private noncomputable def right007Row3 : List ℕ := []

private noncomputable def right007Row4 : List ℕ := []

private noncomputable def right007Row5 : List ℕ := []

private noncomputable def right007Row6 : List ℕ := []

private noncomputable def right007Row7 : List ℕ := []

private noncomputable def rightGaps007 : List (List ℕ) := [right007Row0, right007Row1, right007Row2, right007Row3, right007Row4, right007Row5, right007Row6, right007Row7]

private theorem leftMask007 :
    (leftGaps007.map gapMask == (sourceTransposeB.drop 56).take 8) = true := by
  decide +kernel

private theorem rightMask007 :
    (rightGaps007.map gapMask == (quotientTransposeRows.drop 56).take 8) = true := by
  decide +kernel

private theorem products007 :
    (leftGaps007.map (gapRow quotientTransposeRows) == rightGaps007.map (gapRow targetB)) = true := by
  decide +kernel

theorem block007 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 56).take 8) ((quotientTransposeRows.drop 56).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask007) (beq_iff_eq.mp rightMask007)
    (beq_iff_eq.mp products007)

end QuotientGeneratorBChecks
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
