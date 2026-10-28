module
public meta import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.GapLiteral
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.QuotientGeneratorB.Batch01
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

private noncomputable def left016Row0Part0 : List ℕ := native_gaps% "1,0,0,2,2,1,0,0,3,3,1,0,0,1,1,1,2,0,0,0,0,2,2,2,2,0,2,0,1,0,0,3,1,0,0,1,0,0,0,1,3,0,0,4,1,2,2,1,1,1,1,0,3,0,0,2,4,1,1,0,0,3,0,0,0,1,1,0,1,1,3,0,0,0,6,0,1,0,5,4,1,3,0,0,3,0,1,2,1,0,1,0,0,1,2,1,1,0,3,0,2,3,0,0,0,0,0,1,1,0,1,4" [[]]

private noncomputable def left016Row0 : List ℕ := left016Row0Part0

private noncomputable def left016Row1Part0 : List ℕ := native_gaps% "0,1,5,1,0,0,2,0,0,3,1,2,1,4,0,1,2,5,1,0,0,4,2,0,0,0,2,0,0,0,2,1,0,1,0,1,2,0,0,1,0,0,1,1,0,2,4,0,2,0,0,0,0,0,1,0,0,2,1,0,3,1,0,0,0,3,0,0,0,0,0,1,2,0,0,0,3,0,0,1,0,4,1,2,0,0,1,2,1,2,0,1,1,1,0,0,1,0,1,1,0,1,0,0,1,2,0,1,0,0,0,0,0,0,2,6,3,1,3,0" [[]]

private noncomputable def left016Row1 : List ℕ := left016Row1Part0

private noncomputable def left016Row2Part0 : List ℕ := native_gaps% "6,1,0,0,1,0,0,1,2,0,0,0,2,1,1,1,2,2,1,0,1,0,1,0,1,3,3,1,0,2,0,1,0,2,2,1,3,2,0,1,0,2,0,0,3,1,0,0,2,2,0,2,3,1,0,0,0,0,0,2,2,1,2,2,1,4,0,3,0,4,3,0,1,1,4,1,3,0,0,0,1,1,0,0,2,0,3,5,0,0,0,0,0,0,2,0,0,1,6,1,2,3,1,3,1" [[]]

private noncomputable def left016Row2 : List ℕ := left016Row2Part0

private noncomputable def left016Row3Part0 : List ℕ := native_gaps% "1,1,0,0,1,3,0,0,0,0,0,0,1,0,0,0,0,2,0,2,1,0,0,0,1,1,0,4,0,0,0,0,1,1,1,0,2,0,1,0,0,0,3,0,1,0,2,2,3,1,2,1,9,1,1,0,0,0,0,1,0,0,0,2,0,4,0,0,3,2,0,1,2,0,0,0,0,0,0,0,0,0,1,1,0,2,3,1,0,0,0,0,2,4,1,0,0,2,0,2,1,0,0,3,0,1,0,1,3,1,0,0,0,0,2,1,1,5" [[]]

private noncomputable def left016Row3 : List ℕ := left016Row3Part0

private noncomputable def left016Row4Part0 : List ℕ := native_gaps% "3,0,0,2,0,1,0,1,2,0,0,1,2,1,0,0,4,1,0,1,1,0,0,0,4,2,0,1,0,0,9,0,0,2,2,3,0,0,1,1,1,1,1,2,0,1,2,0,0,4,0,0,0,1,0,3,3,0,0,1,0,1,1,0,0,4,0,2,5,0,0,3,0,1,1,1,1,0,0,0,0,0,0,1,0,0,6,1,0,0,4,0,0,3,0,0,2,0,5,0,2,2,0,0,1,1,0,4,0" [[]]

private noncomputable def left016Row4 : List ℕ := left016Row4Part0

private noncomputable def left016Row5Part0 : List ℕ := native_gaps% "3,2,0,0,0,2,0,4,1,0,0,2,2,1,1,4,1,1,0,0,2,0,2,0,3,1,0,4,6,0,0,0,0,2,0,0,1,1,6,0,2,0,0,2,3,0,1,1,0,2,0,2,3,1,1,0,1,1,0,4,0,4,1,1,1,2,0,1,0,0,0,3,1,1,0,0,0,0,0,3,0,0,2,2,0,0,0,0,4,0,0,0,1,1,0,0,0,0,0,1,1,2,2,1,3,4,0,1,0,0,0,0,0" [[]]

private noncomputable def left016Row5 : List ℕ := left016Row5Part0

private noncomputable def left016Row6Part0 : List ℕ := native_gaps% "0,0,1,1,4,1,0,0,1,2,0,0,1,1,0,1,0,3,1,0,1,0,0,0,2,2,1,3,0,2,1,0,1,0,0,1,0,0,0,5,0,0,1,1,2,1,3,1,0,4,0,2,1,0,2,0,0,1,0,0,0,0,4,3,0,3,2,0,1,1,2,0,4,2,3,2,0,0,0,1,0,0,0,1,0,2,0,1,4,1,0,1,2,0,1,4,3,0,1,1,2,7,1,0,0,2,2,4,0" [[]]

private noncomputable def left016Row6 : List ℕ := left016Row6Part0

private noncomputable def left016Row7Part0 : List ℕ := native_gaps% "0,0,2,2,0,2,0,1,0,0,1,0,0,1,0,0,1,1,0,0,2,2,0,0,2,5,0,4,0,0,0,1,4,1,0,1,0,1,2,1,0,1,3,0,1,1,0,0,0,1,0,2,0,1,1,0,0,0,1,3,2,2,1,1,3,1,0,0,1,1,1,4,0,0,0,0,0,0,3,1,1,1,0,1,1,0,1,4,7,0,4,0,2,1,3,0,0,1,1,1,0,0,4,3,1,5,0,1,0,0,3,0,0" [[]]

private noncomputable def left016Row7 : List ℕ := left016Row7Part0

private noncomputable def leftGaps016 : List (List ℕ) := [left016Row0, left016Row1, left016Row2, left016Row3, left016Row4, left016Row5, left016Row6, left016Row7]

private noncomputable def right016Row0 : List ℕ := []

private noncomputable def right016Row1 : List ℕ := []

private noncomputable def right016Row2 : List ℕ := []

private noncomputable def right016Row3 : List ℕ := []

private noncomputable def right016Row4 : List ℕ := []

private noncomputable def right016Row5 : List ℕ := []

private noncomputable def right016Row6 : List ℕ := []

private noncomputable def right016Row7 : List ℕ := []

private noncomputable def rightGaps016 : List (List ℕ) := [right016Row0, right016Row1, right016Row2, right016Row3, right016Row4, right016Row5, right016Row6, right016Row7]

private theorem leftMask016 :
    (leftGaps016.map gapMask == (sourceTransposeB.drop 128).take 8) = true := by
  decide +kernel

private theorem rightMask016 :
    (rightGaps016.map gapMask == (quotientTransposeRows.drop 128).take 8) = true := by
  decide +kernel

private theorem products016 :
    (leftGaps016.map (gapRow quotientTransposeRows) == rightGaps016.map (gapRow targetB)) = true := by
  decide +kernel

theorem block016 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 128).take 8) ((quotientTransposeRows.drop 128).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask016) (beq_iff_eq.mp rightMask016)
    (beq_iff_eq.mp products016)

private noncomputable def left017Row0Part0 : List ℕ := native_gaps% "0,2,1,1,0,0,0,1,0,0,1,0,0,3,3,0,0,0,1,0,1,3,1,0,3,0,6,0,0,0,0,2,2,0,0,5,1,1,0,0,3,0,0,2,0,0,0,0,0,4,0,0,2,8,4,2,0,1,2,2,1,0,0,0,1,0,2,0,0,1,1,0,2,0,1,0,0,2,2,0,2,1,2,0,1,0,1,0,6,2,2,1,0,1,0,0,1,1,0,1,1,1,1,0,0,3,0,0,1,0,1,0,2,4,0" [[]]

private noncomputable def left017Row0 : List ℕ := left017Row0Part0

private noncomputable def left017Row1Part0 : List ℕ := native_gaps% "0,3,3,0,0,1,2,1,0,0,1,0,1,0,1,1,0,0,1,0,1,0,0,0,0,0,2,0,0,2,2,0,1,7,4,0,0,0,1,2,1,0,1,0,1,0,0,0,0,0,2,0,1,0,2,0,0,2,0,1,3,0,0,0,0,0,0,0,4,0,2,3,0,5,0,0,1,2,0,5,1,2,1,0,1,0,1,3,0,0,0,0,3,5,2,0,0,0,2,0,1,0,4,0,0,0,1,0,0,1,0,1,0,0,2,0,0,0,0,1,1,1" [[]]

private noncomputable def left017Row1 : List ℕ := left017Row1Part0

private noncomputable def left017Row2Part0 : List ℕ := native_gaps% "1,1,1,4,4,4,0,1,1,1,0,0,0,1,0,0,0,0,0,0,2,2,0,2,2,0,0,0,0,3,0,0,0,1,1,2,0,3,1,0,1,0,2,0,2,0,0,5,1,1,3,0,0,1,1,2,1,1,1,0,0,1,1,1,0,2,0,0,0,0,0,0,3,2,0,0,0,1,1,8,0,0,0,2,0,2,2,3,0,6,2,0,4,3,0,0,0,0,0,0,0,0,0,1,1,1,2,1,0,1,0,1,1,1,0,1" [[]]

private noncomputable def left017Row2 : List ℕ := left017Row2Part0

private noncomputable def left017Row3Part0 : List ℕ := native_gaps% "2,1,3,1,0,0,0,0,0,0,2,2,0,0,4,2,1,0,3,0,1,3,0,3,0,1,0,0,1,0,2,2,0,0,4,1,0,0,1,1,2,1,1,1,0,5,0,0,3,0,2,1,0,1,0,2,2,1,0,0,1,0,0,0,1,0,0,2,2,1,0,2,0,1,2,1,2,3,0,2,0,0,0,0,0,0,0,3,3,0,1,1,0,1,1,2,0,1,0,3,2,0,0,0,2,0,0,0,0,1,2,1,2,0,3,1,2" [[]]

private noncomputable def left017Row3 : List ℕ := left017Row3Part0

private noncomputable def left017Row4Part0 : List ℕ := native_gaps% "0,4,1,2,2,0,3,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1,1,0,4,0,3,0,6,2,3,2,0,6,0,0,0,0,1,4,0,0,0,1,0,1,2,3,2,0,0,4,0,2,0,0,1,0,0,0,0,0,2,0,0,0,3,0,0,1,2,1,0,1,0,1,0,2,0,2,0,1,4,0,1,1,0,0,0,0,1,2,1,2,1,3,4,1,0,1,0,0,5,1,1,0,2,1,6" [[]]

private noncomputable def left017Row4 : List ℕ := left017Row4Part0

private noncomputable def left017Row5Part0 : List ℕ := native_gaps% "0,0,2,0,3,4,0,2,0,5,0,0,0,0,0,0,0,0,1,1,1,0,3,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,3,0,5,2,0,0,1,1,1,1,0,0,0,0,1,1,2,0,1,0,1,6,1,0,5,0,1,0,0,1,1,1,3,0,0,5,0,0,0,0,0,6,2,1,0,0,2,0,2,0,1,0,1,0,0,1,4,1,0,0,0,1,0,6,0,1,1,2,0,0,0,1,1,1,0,3,2,0,0,0,4" [[]]

private noncomputable def left017Row5 : List ℕ := left017Row5Part0

private noncomputable def left017Row6Part0 : List ℕ := native_gaps% "0,4,1,3,4,0,0,1,2,2,0,4,2,1,1,1,1,0,0,0,0,2,1,1,3,2,0,1,0,0,0,2,0,3,2,0,8,5,1,2,3,1,1,1,1,0,2,1,2,0,0,2,0,2,1,1,0,1,2,1,1,0,1,0,0,1,0,4,8,1,1,1,3,0,1,0,0,0,1,1,0,1,0,3,2,0,4,0,2,1,2,0,2,0,3,1,0,0,2,0" [[]]

private noncomputable def left017Row6 : List ℕ := left017Row6Part0

private noncomputable def left017Row7Part0 : List ℕ := native_gaps% "0,1,4,2,0,0,0,0,1,0,1,2,0,1,1,0,5,2,0,2,0,2,0,0,0,0,0,2,3,2,2,2,1,0,0,1,1,0,0,2,0,0,2,3,3,1,1,0,0,0,0,1,1,0,2,0,0,0,4,2,1,0,1,0,1,1,3,0,1,0,0,1,1,1,0,2,4,0,1,0,1,3,0,0,1,0,0,0,0,4,0,1,2,2,1,1,0,1,0,3,1,1,3,0,2,0,0,0,2,0,0,0,0,1,0,2,0,3,0" [[]]

private noncomputable def left017Row7 : List ℕ := left017Row7Part0

private noncomputable def leftGaps017 : List (List ℕ) := [left017Row0, left017Row1, left017Row2, left017Row3, left017Row4, left017Row5, left017Row6, left017Row7]

private noncomputable def right017Row0 : List ℕ := []

private noncomputable def right017Row1 : List ℕ := []

private noncomputable def right017Row2 : List ℕ := []

private noncomputable def right017Row3 : List ℕ := []

private noncomputable def right017Row4 : List ℕ := []

private noncomputable def right017Row5 : List ℕ := []

private noncomputable def right017Row6 : List ℕ := []

private noncomputable def right017Row7 : List ℕ := []

private noncomputable def rightGaps017 : List (List ℕ) := [right017Row0, right017Row1, right017Row2, right017Row3, right017Row4, right017Row5, right017Row6, right017Row7]

private theorem leftMask017 :
    (leftGaps017.map gapMask == (sourceTransposeB.drop 136).take 8) = true := by
  decide +kernel

private theorem rightMask017 :
    (rightGaps017.map gapMask == (quotientTransposeRows.drop 136).take 8) = true := by
  decide +kernel

private theorem products017 :
    (leftGaps017.map (gapRow quotientTransposeRows) == rightGaps017.map (gapRow targetB)) = true := by
  decide +kernel

theorem block017 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 136).take 8) ((quotientTransposeRows.drop 136).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask017) (beq_iff_eq.mp rightMask017)
    (beq_iff_eq.mp products017)

private noncomputable def left018Row0Part0 : List ℕ := native_gaps% "0,2,0,0,1,0,0,0,0,0,2,0,1,1,0,0,0,0,0,0,0,0,0,0,1,3,0,6,0,2,0,1,2,1,1,0,6,1,1,1,0,0,1,0,2,0,0,0,0,0,0,1,0,0,0,1,0,2,0,0,1,0,1,6,1,0,2,2,6,1,1,1,0,1,0,2,0,0,2,0,0,1,0,0,0,0,0,0,5,1,1,0,1,2,1,0,0,2,1,0,4,8,1,0,3,0,0,9,2,0,2,1,3,1,0,0" [[]]

private noncomputable def left018Row0 : List ℕ := left018Row0Part0

private noncomputable def left018Row1Part0 : List ℕ := native_gaps% "1,1,0,0,1,0,4,7,0,0,0,1,3,0,1,1,0,0,1,0,0,0,0,3,1,1,1,4,0,3,1,2,1,0,0,1,1,1,0,0,0,0,0,6,2,1,1,1,0,0,0,1,4,0,0,0,3,1,2,0,0,1,2,1,3,0,0,1,0,3,0,0,0,0,1,3,0,1,1,4,0,0,0,3,5,2,0,1,1,0,2,0,0,4,1,0,0,0,0,0,1,0,2,0,1,0,0,0,0,1,4,0,0,1,0,3" [[]]

private noncomputable def left018Row1 : List ℕ := left018Row1Part0

private noncomputable def left018Row2Part0 : List ℕ := native_gaps% "1,0,1,1,0,1,0,5,1,1,0,0,1,0,0,0,1,2,0,2,0,0,0,0,3,2,3,3,3,1,2,0,1,0,0,0,1,0,0,4,2,0,0,3,1,1,4,0,0,0,3,1,0,0,0,2,3,2,0,0,1,0,1,5,0,0,2,0,0,0,7,0,0,0,1,0,0,0,0,0,2,0,0,0,0,2,2,0,0,2,1,0,0,0,0,0,3,1,1,0,1,0,2,0,1,1,0,0,0,9,0,0,0,0,3,3,2" [[]]

private noncomputable def left018Row2 : List ℕ := left018Row2Part0

private noncomputable def left018Row3Part0 : List ℕ := native_gaps% "3,0,0,0,0,4,2,4,2,2,0,0,0,0,1,0,0,0,2,1,0,1,0,0,2,2,0,1,0,9,0,2,1,1,0,2,0,0,3,1,3,1,3,1,0,1,0,0,2,2,2,0,1,0,6,2,0,1,1,0,2,0,0,0,1,2,0,0,0,0,0,0,0,2,6,0,3,0,0,1,0,0,0,0,1,0,2,1,1,1,1,1,1,1,0,1,1,1,1,0,3,0,3,0,2,1,0,1,6,1,1" [[]]

private noncomputable def left018Row3 : List ℕ := left018Row3Part0

private noncomputable def left018Row4Part0 : List ℕ := native_gaps% "0,0,0,1,4,0,0,1,1,1,2,2,4,0,2,3,1,1,1,3,0,0,0,1,0,0,0,2,3,1,1,0,1,2,0,3,0,1,2,1,0,3,0,0,5,0,0,3,1,0,0,0,0,3,2,2,0,2,1,0,0,1,0,0,3,3,1,0,0,1,3,2,4,3,0,0,1,0,5,2,0,1,0,0,1,0,3,2,0,0,1,0,0,2,1,4,0,0,0,1,3,1,0,1,0,0,0,0,1,1" [[]]

private noncomputable def left018Row4 : List ℕ := left018Row4Part0

private noncomputable def left018Row5Part0 : List ℕ := native_gaps% "0,0,2,2,3,2,4,0,1,1,6,0,2,0,2,0,0,0,2,0,1,1,1,0,1,0,0,0,0,3,0,0,0,2,0,2,1,1,0,0,3,0,3,1,1,6,2,0,1,1,0,0,2,0,2,1,2,0,6,0,0,1,2,2,2,1,0,0,4,3,1,0,3,0,1,2,3,1,3,2,0,1,0,4,0,3,0,1,1,2,2,1,0,0,5,0,1,0,0,0,3,1,1,0" [[]]

private noncomputable def left018Row5 : List ℕ := left018Row5Part0

private noncomputable def left018Row6Part0 : List ℕ := native_gaps% "1,0,2,0,0,0,1,1,0,0,1,1,3,0,0,1,0,2,1,0,1,2,0,1,0,2,2,1,0,3,1,0,0,0,0,0,2,1,0,1,2,0,1,0,2,0,0,0,1,2,0,0,1,2,0,3,0,0,1,3,0,2,3,0,0,0,0,0,0,0,0,0,2,3,1,2,2,0,0,4,0,0,0,0,0,0,2,0,0,1,0,0,0,2,0,1,2,0,5,3,0,1,1,0,1,3,0,1,0,2,0,2,1,0,1,0,1,5,0,5,3" [[]]

private noncomputable def left018Row6 : List ℕ := left018Row6Part0

private noncomputable def left018Row7Part0 : List ℕ := native_gaps% "2,1,0,2,1,2,1,3,1,1,3,0,0,2,1,0,2,0,0,1,1,4,4,0,0,1,0,1,0,0,1,2,0,1,1,0,0,1,0,2,3,2,7,2,5,0,1,1,1,0,0,0,0,0,1,0,0,0,0,3,0,0,0,0,0,2,0,1,0,1,2,4,1,0,2,6,5,0,1,0,0,6,6,2,2,2,1,1,0,0,0,0,2,0,0,2,5,0,0,1,0,0,0,0,0,0,0" [[]]

private noncomputable def left018Row7 : List ℕ := left018Row7Part0

private noncomputable def leftGaps018 : List (List ℕ) := [left018Row0, left018Row1, left018Row2, left018Row3, left018Row4, left018Row5, left018Row6, left018Row7]

private noncomputable def right018Row0 : List ℕ := []

private noncomputable def right018Row1 : List ℕ := []

private noncomputable def right018Row2 : List ℕ := []

private noncomputable def right018Row3 : List ℕ := []

private noncomputable def right018Row4 : List ℕ := []

private noncomputable def right018Row5 : List ℕ := []

private noncomputable def right018Row6 : List ℕ := []

private noncomputable def right018Row7 : List ℕ := []

private noncomputable def rightGaps018 : List (List ℕ) := [right018Row0, right018Row1, right018Row2, right018Row3, right018Row4, right018Row5, right018Row6, right018Row7]

private theorem leftMask018 :
    (leftGaps018.map gapMask == (sourceTransposeB.drop 144).take 8) = true := by
  decide +kernel

private theorem rightMask018 :
    (rightGaps018.map gapMask == (quotientTransposeRows.drop 144).take 8) = true := by
  decide +kernel

private theorem products018 :
    (leftGaps018.map (gapRow quotientTransposeRows) == rightGaps018.map (gapRow targetB)) = true := by
  decide +kernel

theorem block018 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 144).take 8) ((quotientTransposeRows.drop 144).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask018) (beq_iff_eq.mp rightMask018)
    (beq_iff_eq.mp products018)

private noncomputable def left019Row0Part0 : List ℕ := native_gaps% "0,7,0,2,1,0,1,1,0,1,1,0,3,0,0,0,1,0,0,0,0,0,2,1,2,0,0,0,2,3,0,5,0,0,0,0,1,0,2,1,4,2,1,1,2,1,0,0,3,0,3,1,0,0,0,1,1,0,0,2,2,2,3,3,0,0,1,3,0,3,1,1,0,0,1,1,0,1,0,2,0,1,0,0,2,0,2,0,0,1,0,0,3,0,1,0,1,0,0,2,3,0,1,1,3,0,2,5,9,0" [[]]

private noncomputable def left019Row0 : List ℕ := left019Row0Part0

private noncomputable def left019Row1Part0 : List ℕ := native_gaps% "1,2,0,2,2,3,1,0,0,0,4,2,0,1,1,0,5,0,0,4,1,3,0,1,3,0,0,0,2,2,0,1,3,0,0,0,3,1,0,0,0,1,2,0,4,2,1,0,1,1,0,0,0,0,7,2,1,1,1,0,1,0,0,4,0,1,2,1,5,0,0,4,0,2,0,0,0,0,1,2,0,1,0,0,1,0,0,1,0,1,5,0,2,0,2,0,2,1,0,4,4,1,2,0,0,1,2" [[]]

private noncomputable def left019Row1 : List ℕ := left019Row1Part0

private noncomputable def left019Row2Part0 : List ℕ := native_gaps% "3,0,0,2,1,3,0,1,0,1,0,1,1,5,1,0,0,2,0,0,2,3,0,0,1,0,1,7,0,0,0,1,0,0,0,0,0,0,1,0,1,2,2,1,0,0,0,0,0,0,1,0,2,2,0,2,1,0,1,2,1,3,1,5,0,1,1,0,0,2,0,2,1,0,0,1,2,0,5,0,0,0,0,1,1,0,1,0,2,1,1,0,4,0,0,0,0,0,6,0,1,0,3,0,3,0,0,7,2,3,2,2,0" [[]]

private noncomputable def left019Row2 : List ℕ := left019Row2Part0

private noncomputable def left019Row3Part0 : List ℕ := native_gaps% "0,1,2,0,0,2,0,1,4,0,3,0,1,1,0,3,0,1,1,1,0,2,6,0,0,5,0,0,2,0,0,0,0,0,5,0,0,0,1,2,0,1,2,0,1,0,0,0,0,1,0,1,2,2,0,7,0,0,0,2,0,0,0,1,0,2,0,0,0,1,1,0,0,0,2,1,0,0,2,1,0,4,2,2,2,4,2,0,0,3,1,0,0,1,0,0,1,0,2,1,3,0,1,0,0,1,5,0,1,0,1,1,0,0,2,0" [[]]

private noncomputable def left019Row3 : List ℕ := left019Row3Part0

private noncomputable def left019Row4Part0 : List ℕ := native_gaps% "0,0,0,0,0,1,1,0,3,3,0,3,0,3,4,1,0,1,4,2,1,1,0,0,0,3,0,0,1,0,0,3,0,0,1,4,1,3,0,0,6,2,1,0,1,1,0,0,1,0,0,0,0,0,1,1,2,1,0,1,1,0,0,0,3,1,0,1,0,0,1,0,1,4,1,1,3,3,3,0,3,0,1,0,1,0,2,0,3,1,0,0,1,0,1,0,0,1,2,12,0,0,0,0,0,2,0,1,0,1,0,1" [[]]

private noncomputable def left019Row4 : List ℕ := left019Row4Part0

private noncomputable def left019Row5Part0 : List ℕ := native_gaps% "0,0,2,0,0,0,4,1,0,0,1,0,1,1,1,1,0,1,3,1,0,0,0,5,1,1,0,1,3,0,1,1,3,2,0,2,0,2,1,0,3,0,0,0,0,0,1,5,1,1,0,0,1,5,1,0,0,0,1,2,0,0,1,0,0,2,0,3,3,2,1,1,2,1,3,1,0,1,0,1,1,0,0,0,0,3,0,2,0,0,0,1,4,3,1,2,1,0,2,0,5,0,0,4,0,0,3,0,0,1,0,0,1,0,0" [[]]

private noncomputable def left019Row5 : List ℕ := left019Row5Part0

private noncomputable def left019Row6Part0 : List ℕ := native_gaps% "1,0,0,5,1,2,4,1,0,4,3,1,0,0,1,2,2,2,0,0,0,1,0,1,1,2,1,1,0,0,2,0,0,5,0,0,0,0,4,0,0,1,0,3,6,0,0,1,0,0,0,0,1,0,1,0,2,0,0,5,0,0,0,0,0,0,6,0,0,0,0,4,1,1,1,0,0,5,0,2,2,0,0,0,1,0,0,0,0,0,0,0,1,0,1,6,1,0,0,0,0,1,0,0,0,0,1,5,2,0,0,1,0,0,0,1,1,0,2" [[]]

private noncomputable def left019Row6 : List ℕ := left019Row6Part0

private noncomputable def left019Row7Part0 : List ℕ := native_gaps% "2,0,0,0,1,1,0,3,0,4,2,0,0,3,1,0,0,0,1,3,1,2,1,0,1,0,1,1,1,2,1,0,4,0,0,1,2,2,2,0,0,1,2,0,0,0,0,0,0,2,0,0,0,0,0,1,0,0,0,1,5,0,0,0,2,1,2,0,0,0,0,0,1,1,0,0,3,0,1,3,0,1,0,0,1,1,1,1,1,1,0,1,3,6,0,0,2,2,1,0,1,0,1,1,0,0,3,0,1,0,2,1,0,1,0,0,0,0,0,2,2,1,2" [[]]

private noncomputable def left019Row7 : List ℕ := left019Row7Part0

private noncomputable def leftGaps019 : List (List ℕ) := [left019Row0, left019Row1, left019Row2, left019Row3, left019Row4, left019Row5, left019Row6, left019Row7]

private noncomputable def right019Row0 : List ℕ := []

private noncomputable def right019Row1 : List ℕ := []

private noncomputable def right019Row2 : List ℕ := []

private noncomputable def right019Row3 : List ℕ := []

private noncomputable def right019Row4 : List ℕ := []

private noncomputable def right019Row5 : List ℕ := []

private noncomputable def right019Row6 : List ℕ := []

private noncomputable def right019Row7 : List ℕ := []

private noncomputable def rightGaps019 : List (List ℕ) := [right019Row0, right019Row1, right019Row2, right019Row3, right019Row4, right019Row5, right019Row6, right019Row7]

private theorem leftMask019 :
    (leftGaps019.map gapMask == (sourceTransposeB.drop 152).take 8) = true := by
  decide +kernel

private theorem rightMask019 :
    (rightGaps019.map gapMask == (quotientTransposeRows.drop 152).take 8) = true := by
  decide +kernel

private theorem products019 :
    (leftGaps019.map (gapRow quotientTransposeRows) == rightGaps019.map (gapRow targetB)) = true := by
  decide +kernel

theorem block019 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 152).take 8) ((quotientTransposeRows.drop 152).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask019) (beq_iff_eq.mp rightMask019)
    (beq_iff_eq.mp products019)

private noncomputable def left020Row0Part0 : List ℕ := native_gaps% "0,0,0,4,0,1,0,0,1,0,1,1,1,3,0,1,4,2,2,0,0,0,2,1,0,1,1,0,0,1,3,0,0,1,2,2,2,1,0,1,0,1,0,1,0,0,0,6,3,0,0,0,7,2,0,0,2,1,0,0,3,0,0,0,3,1,0,0,0,7,2,0,0,1,0,1,0,0,0,0,0,1,2,1,1,3,1,1,0,1,0,2,0,6,2,0,0,3,0,0,1,0,2,4,4,0,0,0,3,2,0,0" [[]]

private noncomputable def left020Row0 : List ℕ := left020Row0Part0

private noncomputable def left020Row1Part0 : List ℕ := native_gaps% "1,0,1,2,1,0,0,0,1,0,1,1,0,1,0,1,0,0,1,1,1,0,0,0,2,0,0,1,0,3,2,0,0,0,5,2,1,0,0,2,0,0,0,0,5,0,2,2,0,1,0,0,2,0,2,2,1,0,0,3,1,0,0,3,8,1,2,1,2,2,0,0,3,1,1,0,1,5,1,0,1,0,0,0,1,1,1,1,0,1,0,0,1,0,5,0,0,3,1,0,3,1,1,0,3,2,0,0,0,0,0,0,4,3,1" [[]]

private noncomputable def left020Row1 : List ℕ := left020Row1Part0

private noncomputable def left020Row2Part0 : List ℕ := native_gaps% "2,2,2,3,2,1,1,3,2,1,0,1,1,0,2,1,0,0,0,2,0,2,0,1,7,0,0,2,4,0,1,0,1,0,0,1,0,2,0,0,0,2,2,0,0,1,0,0,0,0,2,5,0,3,0,0,0,1,0,1,1,2,2,0,0,7,0,0,0,0,3,0,0,1,0,5,0,0,0,0,0,0,0,0,1,1,1,0,0,0,1,0,0,2,1,1,0,0,1,2,0,3,0,1,0,1,3,0,0,2,1,1,2,0,0,1" [[]]

private noncomputable def left020Row2 : List ℕ := left020Row2Part0

private noncomputable def left020Row3Part1 : List ℕ := native_gaps% "0" [[]]

private noncomputable def left020Row3Part0 : List ℕ := native_gaps% "2,1,1,0,0,0,0,1,0,2,1,0,0,0,1,0,0,1,0,2,0,0,0,1,0,1,0,2,3,0,1,0,2,1,0,0,0,1,0,1,0,0,0,0,1,0,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,1,1,0,1,2,0,0,2,0,0,1,1,1,3,2,0,0,2,1,0,0,0,1,0,1,0,2,3,7,0,2,4,1,0,1,1,0,1,2,2,5,0,0,0,2,2,3,1,0,1,0,4,3,0,0,0,1,0,0,0,0,3,1,0,0,0,2" [left020Row3Part1]

private noncomputable def left020Row3 : List ℕ := left020Row3Part0

private noncomputable def left020Row4Part0 : List ℕ := native_gaps% "2,3,2,0,3,1,1,0,0,1,1,2,1,4,3,0,3,2,1,0,2,0,0,1,3,1,0,0,0,0,1,1,1,4,4,0,1,0,6,0,0,0,0,1,2,0,0,1,0,2,1,3,1,3,2,0,1,0,0,1,2,1,0,0,0,0,0,2,0,2,0,3,0,1,0,0,1,2,0,2,0,2,1,1,0,2,0,2,0,0,0,6,1,2,0,0,0,0,2,1,0,2,2,0,2,2,0,0,0,0,0" [[]]

private noncomputable def left020Row4 : List ℕ := left020Row4Part0

private noncomputable def left020Row5Part0 : List ℕ := native_gaps% "0,0,0,1,0,1,0,1,1,1,1,3,2,0,2,0,0,0,0,1,2,0,0,1,0,1,5,0,3,0,1,1,0,2,0,0,1,0,0,0,0,1,0,1,0,0,0,2,3,0,1,3,0,8,0,2,0,0,0,3,1,0,2,1,0,1,0,4,2,4,0,1,1,0,0,1,0,2,0,0,0,1,1,4,1,0,0,0,0,0,0,2,0,0,0,4,7,0,0,1,0,0,0,0,2,0,2,2,0,0,1,0,0,0,0,1,0,2,0,3,0,1" [[]]

private noncomputable def left020Row5 : List ℕ := left020Row5Part0

private noncomputable def left020Row6Part0 : List ℕ := native_gaps% "1,0,0,4,0,1,3,2,1,4,0,4,0,0,2,4,0,0,2,2,0,3,3,3,0,0,2,0,0,5,1,0,2,1,1,2,1,0,1,1,0,4,1,0,2,0,1,1,1,2,3,0,2,0,4,2,0,4,3,0,0,0,0,0,2,0,0,0,3,4,2,0,0,0,0,1,5,1,2,1,0,0,0,0,2,0,1,0,0,1,0,1,1,3,1,0,1,1,1,2,1,1,0,0,0,2" [[]]

private noncomputable def left020Row6 : List ℕ := left020Row6Part0

private noncomputable def left020Row7Part0 : List ℕ := native_gaps% "1,0,2,0,0,1,3,1,0,1,3,1,1,1,2,0,0,3,3,0,1,3,0,2,0,0,1,0,0,0,0,0,0,0,0,1,2,2,0,0,0,0,2,0,1,0,3,0,1,0,1,0,3,0,0,3,1,1,0,0,0,0,0,5,0,1,1,0,0,0,1,0,1,1,1,0,3,0,8,0,0,1,0,3,0,2,1,2,1,0,1,0,0,2,2,2,1,0,1,0,0,4,2,0,0,1,2,1,0,0,0,0,3,0,0,0,0,2,0,0,0,0,0" [[]]

private noncomputable def left020Row7 : List ℕ := left020Row7Part0

private noncomputable def leftGaps020 : List (List ℕ) := [left020Row0, left020Row1, left020Row2, left020Row3, left020Row4, left020Row5, left020Row6, left020Row7]

private noncomputable def right020Row0 : List ℕ := []

private noncomputable def right020Row1 : List ℕ := []

private noncomputable def right020Row2 : List ℕ := []

private noncomputable def right020Row3 : List ℕ := []

private noncomputable def right020Row4 : List ℕ := []

private noncomputable def right020Row5 : List ℕ := []

private noncomputable def right020Row6 : List ℕ := []

private noncomputable def right020Row7 : List ℕ := []

private noncomputable def rightGaps020 : List (List ℕ) := [right020Row0, right020Row1, right020Row2, right020Row3, right020Row4, right020Row5, right020Row6, right020Row7]

private theorem leftMask020 :
    (leftGaps020.map gapMask == (sourceTransposeB.drop 160).take 8) = true := by
  decide +kernel

private theorem rightMask020 :
    (rightGaps020.map gapMask == (quotientTransposeRows.drop 160).take 8) = true := by
  decide +kernel

private theorem products020 :
    (leftGaps020.map (gapRow quotientTransposeRows) == rightGaps020.map (gapRow targetB)) = true := by
  decide +kernel

theorem block020 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 160).take 8) ((quotientTransposeRows.drop 160).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask020) (beq_iff_eq.mp rightMask020)
    (beq_iff_eq.mp products020)

private noncomputable def left021Row0Part0 : List ℕ := native_gaps% "0,0,0,2,4,1,0,1,0,4,0,0,0,0,0,0,1,0,0,3,2,2,0,0,0,0,0,0,0,3,3,0,0,0,0,0,0,2,1,1,1,1,1,2,1,0,3,0,2,1,2,0,0,0,0,2,0,0,1,1,0,0,0,1,0,0,0,1,2,1,0,0,1,0,0,1,0,0,0,0,0,0,0,4,0,0,1,0,0,0,0,1,0,0,0,5,1,1,0,3,1,0,3,6,0,0,0,1,4,1,3,0,1,1,2,0,6,0,0,1,1,0,0,1,1" [[]]

private noncomputable def left021Row0 : List ℕ := left021Row0Part0

private noncomputable def left021Row1Part0 : List ℕ := native_gaps% "1,2,0,1,2,0,0,0,1,2,1,1,1,0,2,0,0,1,1,1,1,0,4,0,0,1,0,2,0,2,0,0,0,0,2,1,1,0,2,2,0,0,0,1,2,1,0,3,0,0,1,4,5,1,2,2,0,0,1,2,0,0,1,0,2,1,0,0,0,0,0,2,2,0,5,0,0,0,0,0,0,1,1,1,0,1,0,0,0,1,3,2,0,1,2,8,0,4,0,3,1,0,2,3,1,4,1,6,0,2" [[]]

private noncomputable def left021Row1 : List ℕ := left021Row1Part0

private noncomputable def left021Row2Part0 : List ℕ := native_gaps% "0,2,3,2,0,5,0,0,0,3,0,0,3,1,2,0,0,1,2,2,2,0,3,4,0,1,1,2,0,2,0,0,0,2,0,0,5,2,2,0,0,2,0,0,2,0,5,0,0,0,0,3,4,3,0,0,3,2,0,0,1,1,0,0,0,3,6,0,2,2,2,4,0,0,6,3,1,2,1,1,1,0,1,0,1,0,1,1,0,1,0,0,0,0,1,1,1,0,1,2,3,0,2" [[]]

private noncomputable def left021Row2 : List ℕ := left021Row2Part0

private noncomputable def left021Row3Part0 : List ℕ := native_gaps% "7,0,1,6,2,0,2,0,0,1,4,2,4,0,2,0,0,1,0,2,0,4,3,2,2,3,1,0,0,0,3,0,3,1,4,2,0,5,0,1,3,1,3,0,0,2,4,0,2,1,0,1,0,2,0,0,1,2,1,4,1,1,0,1,0,2,0,0,0,2,0,0,2,0,0,2,0,1,0,3,1,0,0,0,0,0,2,1,0,0,0,0,7,0,0,0,4,0,0,3,0,0,0,0" [[]]

private noncomputable def left021Row3 : List ℕ := left021Row3Part0

private noncomputable def left021Row4Part0 : List ℕ := native_gaps% "0,1,3,1,1,2,0,2,0,0,0,1,1,1,2,0,0,2,0,2,0,0,0,0,1,1,0,1,5,0,4,1,3,0,2,0,4,1,1,0,0,1,1,2,2,0,0,1,0,2,1,1,0,2,1,0,6,0,1,0,0,0,2,1,4,1,0,3,0,1,1,0,0,1,1,0,0,0,0,0,3,0,0,0,0,0,2,2,0,1,1,0,0,2,3,3,0,3,0,2,0,4,3,2,0,0,4,2,3,2,0" [[]]

private noncomputable def left021Row4 : List ℕ := left021Row4Part0

private noncomputable def left021Row5Part0 : List ℕ := native_gaps% "3,0,1,0,1,0,5,0,1,1,0,1,2,7,0,0,4,0,0,2,0,1,1,0,0,0,1,5,1,0,4,5,0,0,0,2,0,1,2,1,4,3,0,1,1,0,0,3,0,4,1,0,0,0,0,1,1,1,0,0,0,8,0,0,0,1,0,1,4,0,1,1,0,2,0,1,2,3,2,0,4,0,6,1,0,0,3,0,1,1,0,0,2,0,0,2,0,0,2,0,0,1,4,1,0" [[]]

private noncomputable def left021Row5 : List ℕ := left021Row5Part0

private noncomputable def left021Row6Part0 : List ℕ := native_gaps% "0,0,0,0,0,1,0,4,1,0,2,0,1,0,5,1,0,2,1,1,7,2,2,1,0,1,0,0,1,3,1,1,1,2,2,0,0,0,0,1,0,3,2,2,0,0,0,0,2,0,0,1,0,0,5,9,0,4,0,0,1,1,0,2,2,0,0,0,0,0,4,0,0,0,2,1,3,3,1,0,2,0,2,0,0,0,1,0,0,0,0,1,5,0,1,0,0,0,0,1,0,0,3,4,0,1,1,1,0,0,0,0,3,0" [[]]

private noncomputable def left021Row6 : List ℕ := left021Row6Part0

private noncomputable def left021Row7Part0 : List ℕ := native_gaps% "0,0,2,1,0,4,2,1,1,5,0,0,0,2,0,0,0,2,0,1,0,1,3,1,0,2,0,3,0,2,1,1,0,0,0,1,0,1,0,0,0,3,0,2,1,1,1,1,2,0,1,0,0,3,2,3,1,0,0,0,0,1,0,1,0,1,0,3,0,1,4,0,0,1,0,0,1,1,4,2,3,1,0,0,2,2,3,0,2,0,0,2,0,1,0,0,1,2,1,2,0,0,4,0,0,4,0,2,0,0,2,3,3" [[]]

private noncomputable def left021Row7 : List ℕ := left021Row7Part0

private noncomputable def leftGaps021 : List (List ℕ) := [left021Row0, left021Row1, left021Row2, left021Row3, left021Row4, left021Row5, left021Row6, left021Row7]

private noncomputable def right021Row0 : List ℕ := []

private noncomputable def right021Row1 : List ℕ := []

private noncomputable def right021Row2 : List ℕ := []

private noncomputable def right021Row3 : List ℕ := []

private noncomputable def right021Row4 : List ℕ := []

private noncomputable def right021Row5 : List ℕ := []

private noncomputable def right021Row6 : List ℕ := []

private noncomputable def right021Row7 : List ℕ := []

private noncomputable def rightGaps021 : List (List ℕ) := [right021Row0, right021Row1, right021Row2, right021Row3, right021Row4, right021Row5, right021Row6, right021Row7]

private theorem leftMask021 :
    (leftGaps021.map gapMask == (sourceTransposeB.drop 168).take 8) = true := by
  decide +kernel

private theorem rightMask021 :
    (rightGaps021.map gapMask == (quotientTransposeRows.drop 168).take 8) = true := by
  decide +kernel

private theorem products021 :
    (leftGaps021.map (gapRow quotientTransposeRows) == rightGaps021.map (gapRow targetB)) = true := by
  decide +kernel

theorem block021 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 168).take 8) ((quotientTransposeRows.drop 168).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask021) (beq_iff_eq.mp rightMask021)
    (beq_iff_eq.mp products021)

private noncomputable def left022Row0Part0 : List ℕ := native_gaps% "2,3,1,0,0,3,1,1,3,3,2,1,0,0,0,0,0,1,0,0,0,1,1,0,0,0,6,3,7,0,0,1,2,0,0,1,2,0,2,1,1,2,0,2,1,0,0,3,0,0,1,0,0,2,0,0,0,0,1,0,1,1,0,1,0,0,0,1,2,0,1,0,0,5,2,0,2,4,0,0,4,1,0,0,1,6,3,2,0,0,1,2,0,0,0,0,0,1,0,1,0,0,0,0,0,3,2,2,0,0,2,5,0" [[]]

private noncomputable def left022Row0 : List ℕ := left022Row0Part0

private noncomputable def left022Row1Part0 : List ℕ := native_gaps% "2,0,1,2,6,0,3,0,0,3,0,3,1,1,1,0,1,3,0,0,2,1,0,1,0,0,2,0,1,0,0,1,0,5,1,2,0,0,1,4,2,0,2,0,0,0,3,0,0,1,0,1,0,0,2,0,1,2,1,1,0,0,0,0,1,1,4,3,0,0,0,0,0,0,0,1,0,1,1,0,1,0,0,0,1,0,1,0,0,2,0,1,0,5,0,0,0,1,0,3,0,0,0,0,2,4,2,0,1,0,0,0,2,4,1,2,0,5" [[]]

private noncomputable def left022Row1 : List ℕ := left022Row1Part0

private noncomputable def left022Row2Part0 : List ℕ := native_gaps% "0,2,0,0,1,1,1,0,2,3,0,0,2,0,0,2,1,1,0,0,1,0,1,1,5,1,0,0,1,1,0,1,4,0,0,5,0,1,1,1,1,4,1,1,0,0,1,1,4,0,2,1,0,0,0,3,1,5,0,2,0,0,2,1,1,1,1,0,0,0,0,3,0,0,2,0,1,1,2,1,1,0,1,5,0,0,0,2,1,0,0,0,1,0,0,0,1,0,0,1,0,0,0,0,2,1,0,1,0,4,0,2,2,2,0,0,1,0,0,0" [[]]

private noncomputable def left022Row2 : List ℕ := left022Row2Part0

private noncomputable def left022Row3Part0 : List ℕ := native_gaps% "1,1,0,2,2,2,0,0,0,0,1,0,2,0,0,0,0,1,0,0,0,0,0,1,1,0,0,1,2,1,0,1,1,1,0,1,0,0,0,1,2,4,2,2,0,1,0,1,2,2,0,2,0,0,0,4,2,1,3,0,4,1,0,2,0,3,1,0,0,2,0,1,4,0,0,0,2,0,2,4,1,3,0,0,0,1,5,1,0,1,2,0,0,1,0,0,2,2,1,0,4,1,3,0,0,3,1,0,0,0,7,1,0,0" [[]]

private noncomputable def left022Row3 : List ℕ := left022Row3Part0

private noncomputable def left022Row4Part0 : List ℕ := native_gaps% "5,0,0,2,0,1,1,0,1,1,2,0,6,0,4,1,0,0,0,6,1,3,0,0,6,2,2,5,0,1,0,3,0,4,0,0,1,0,2,5,2,1,0,0,0,0,1,0,5,0,3,1,0,1,0,1,1,0,0,0,2,2,1,0,2,0,0,0,0,1,2,1,0,1,2,1,2,1,0,2,2,0,0,2,0,1,3,0,0,0,0,1,3,0,1,3,1,0,0,1,1,0,1,1,0,2" [[]]

private noncomputable def left022Row4 : List ℕ := left022Row4Part0

private noncomputable def left022Row5Part0 : List ℕ := native_gaps% "0,0,0,0,0,1,3,5,1,3,0,0,0,1,1,1,0,1,1,1,0,0,0,2,1,0,0,2,1,4,0,1,1,1,2,0,1,0,0,5,0,0,0,5,0,0,6,0,2,0,0,1,0,0,0,5,0,0,0,0,0,0,1,0,0,4,3,2,0,0,0,0,2,2,0,0,0,1,0,1,3,2,0,1,0,3,0,4,0,0,3,1,2,3,0,0,1,0,3,0,0,6,0,0,0,0,0,1,1,0,4,0,5,0" [[]]

private noncomputable def left022Row5 : List ℕ := left022Row5Part0

private noncomputable def left022Row6Part0 : List ℕ := native_gaps% "1,0,0,0,0,1,1,1,0,1,0,1,1,1,0,0,1,0,0,0,0,2,2,0,0,2,0,0,1,2,1,0,2,1,0,2,0,0,0,1,1,0,0,2,1,0,0,1,1,1,2,0,0,0,1,0,0,0,0,0,1,1,1,0,0,3,5,5,6,0,0,1,0,2,0,1,5,3,2,0,2,1,0,5,5,2,1,0,0,2,0,0,1,1,1,2,0,3,1,1,1,1,0,4,0,0,1,0,0,1,0,0,0,4,1,3,0" [[]]

private noncomputable def left022Row6 : List ℕ := left022Row6Part0

private noncomputable def left022Row7Part0 : List ℕ := native_gaps% "1,0,2,2,0,0,4,2,2,3,0,0,0,1,0,2,2,2,0,6,0,2,3,0,3,1,1,6,1,0,0,0,6,2,0,1,0,1,0,0,0,0,1,0,2,0,0,3,0,1,1,3,0,1,3,1,0,3,3,3,0,1,0,0,0,0,4,1,0,1,0,1,4,1,0,0,0,1,1,0,3,5,0,0,1,1,0,0,0,1,1,2,0,0,0,1,1,0,3,5,2,0,0,0,0,0,0,0,0,0" [[]]

private noncomputable def left022Row7 : List ℕ := left022Row7Part0

private noncomputable def leftGaps022 : List (List ℕ) := [left022Row0, left022Row1, left022Row2, left022Row3, left022Row4, left022Row5, left022Row6, left022Row7]

private noncomputable def right022Row0 : List ℕ := []

private noncomputable def right022Row1 : List ℕ := []

private noncomputable def right022Row2 : List ℕ := []

private noncomputable def right022Row3 : List ℕ := []

private noncomputable def right022Row4 : List ℕ := []

private noncomputable def right022Row5 : List ℕ := []

private noncomputable def right022Row6 : List ℕ := []

private noncomputable def right022Row7 : List ℕ := []

private noncomputable def rightGaps022 : List (List ℕ) := [right022Row0, right022Row1, right022Row2, right022Row3, right022Row4, right022Row5, right022Row6, right022Row7]

private theorem leftMask022 :
    (leftGaps022.map gapMask == (sourceTransposeB.drop 176).take 8) = true := by
  decide +kernel

private theorem rightMask022 :
    (rightGaps022.map gapMask == (quotientTransposeRows.drop 176).take 8) = true := by
  decide +kernel

private theorem products022 :
    (leftGaps022.map (gapRow quotientTransposeRows) == rightGaps022.map (gapRow targetB)) = true := by
  decide +kernel

theorem block022 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 176).take 8) ((quotientTransposeRows.drop 176).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask022) (beq_iff_eq.mp rightMask022)
    (beq_iff_eq.mp products022)

private noncomputable def left023Row0Part0 : List ℕ := native_gaps% "0,1,0,0,2,0,2,0,1,0,1,0,0,3,0,1,3,1,2,4,1,3,0,3,0,0,1,1,2,2,0,0,2,1,0,0,0,0,1,1,0,2,0,0,1,0,0,0,0,1,3,1,0,1,0,0,0,1,0,0,1,0,0,0,1,0,0,1,0,0,1,1,5,1,0,0,0,0,0,13,2,3,1,1,2,0,0,1,6,0,0,5,0,3,0,0,2,1,0,0,0,1,0,0,2,0,6,0,1,0,0,0,2,1,0,0" [[]]

private noncomputable def left023Row0 : List ℕ := left023Row0Part0

private noncomputable def left023Row1Part0 : List ℕ := native_gaps% "3,4,0,1,1,0,0,0,0,2,1,1,0,2,0,1,0,1,3,3,2,1,0,3,0,0,0,2,0,0,0,0,1,3,0,0,0,0,0,0,0,0,3,1,0,0,2,1,4,2,3,0,0,0,1,1,0,1,2,0,1,0,1,0,0,0,0,1,1,5,0,0,1,1,0,0,0,1,0,0,0,3,0,4,0,2,0,3,0,1,1,1,0,0,1,2,0,1,0,0,0,0,0,1,0,0,5,2,1,2,0,4,1,1,3,0,1,0,2,0,0,0" [[]]

private noncomputable def left023Row1 : List ℕ := left023Row1Part0

private noncomputable def left023Row2Part0 : List ℕ := native_gaps% "0,1,0,3,0,1,5,0,1,0,0,0,3,1,1,0,2,2,2,1,0,2,0,0,0,0,4,1,0,0,0,2,1,0,0,2,0,0,4,2,0,0,1,0,0,3,2,0,4,1,0,2,0,0,0,5,3,0,0,2,9,1,3,0,0,0,2,1,0,3,0,1,0,0,0,0,1,0,1,0,1,1,0,0,2,2,0,0,2,1,1,1,0,1,0,0,0,0,0,1,0,3,1,2,1,0,0,2,1,0,2,1,0,0,1,3" [[]]

private noncomputable def left023Row2 : List ℕ := left023Row2Part0

private noncomputable def left023Row3Part0 : List ℕ := native_gaps% "0,2,1,1,4,1,0,1,1,0,1,0,0,0,0,0,1,1,0,0,1,1,6,0,0,1,0,1,0,1,2,0,0,1,0,0,0,0,0,0,5,0,3,8,1,2,0,2,0,2,0,0,0,1,0,0,1,0,4,0,1,4,1,0,2,0,0,2,0,0,1,3,0,1,2,2,0,1,2,1,0,0,1,4,0,1,1,0,0,1,2,0,5,1,1,0,0,1,0,3,0,3,0,1,1,0,0,0,4,0,0,0,2,2,0,2" [[]]

private noncomputable def left023Row3 : List ℕ := left023Row3Part0

private noncomputable def left023Row4Part0 : List ℕ := native_gaps% "0,1,1,1,1,1,1,2,0,1,0,0,1,0,1,0,1,3,1,0,0,0,0,1,0,3,5,1,0,0,3,0,0,0,1,0,0,1,0,0,2,0,1,4,0,0,0,0,1,3,2,0,0,0,1,0,2,0,1,0,0,0,0,0,2,1,1,0,0,0,5,0,7,1,0,0,4,0,0,1,1,1,0,1,0,0,1,1,1,1,0,0,0,0,1,0,2,0,1,0,1,0,0,0,0,2,3,0,3,1,1,2,8,1,0,2,0,0,1,0,1,0,0,0,0" [[]]

private noncomputable def left023Row4 : List ℕ := left023Row4Part0

private noncomputable def left023Row5Part0 : List ℕ := native_gaps% "0,0,9,0,0,0,2,2,2,0,1,2,0,0,1,2,2,2,2,0,1,0,3,5,2,1,0,1,0,1,0,1,1,0,0,0,3,0,0,0,1,1,0,2,0,0,0,0,0,2,4,0,0,4,0,0,1,0,0,3,0,1,1,0,2,2,0,0,0,0,0,4,0,0,1,1,7,0,1,0,3,3,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,1,0,2,0,2,0,0,1,0,1,1,0,0,1,2,1,0,1,2,1,0,0" [[]]

private noncomputable def left023Row5 : List ℕ := left023Row5Part0

private noncomputable def left023Row6Part0 : List ℕ := native_gaps% "0,0,0,4,2,2,2,0,2,1,1,0,0,0,0,0,0,2,1,1,1,1,3,2,0,0,2,0,1,1,1,0,0,0,4,2,0,2,0,1,1,0,0,2,2,2,0,5,0,0,3,0,1,4,0,1,4,0,2,0,0,1,3,2,0,0,4,0,1,0,2,0,5,1,0,0,1,5,1,0,1,2,0,3,2,0,1,3,0,0,2,1,1,4,0,7,2,0,2,0,1,0,0,0,0" [[]]

private noncomputable def left023Row6 : List ℕ := left023Row6Part0

private noncomputable def left023Row7Part0 : List ℕ := native_gaps% "0,0,1,1,1,0,0,0,0,1,0,2,0,0,6,0,4,1,2,1,0,1,1,1,0,1,2,1,1,0,1,3,0,1,0,1,0,0,0,2,0,0,3,1,0,2,0,0,2,1,0,1,0,2,0,1,0,1,0,2,2,0,0,1,0,1,1,2,1,0,0,1,0,0,0,1,1,7,1,0,0,0,0,0,2,1,1,0,0,2,3,0,1,2,2,0,0,0,1,0,0,0,3,3,0,3,0,0,0,0,0,1,6,3,0,0,4,0,3" [[]]

private noncomputable def left023Row7 : List ℕ := left023Row7Part0

private noncomputable def leftGaps023 : List (List ℕ) := [left023Row0, left023Row1, left023Row2, left023Row3, left023Row4, left023Row5, left023Row6, left023Row7]

private noncomputable def right023Row0 : List ℕ := []

private noncomputable def right023Row1 : List ℕ := []

private noncomputable def right023Row2 : List ℕ := []

private noncomputable def right023Row3 : List ℕ := []

private noncomputable def right023Row4 : List ℕ := []

private noncomputable def right023Row5 : List ℕ := []

private noncomputable def right023Row6 : List ℕ := []

private noncomputable def right023Row7 : List ℕ := []

private noncomputable def rightGaps023 : List (List ℕ) := [right023Row0, right023Row1, right023Row2, right023Row3, right023Row4, right023Row5, right023Row6, right023Row7]

private theorem leftMask023 :
    (leftGaps023.map gapMask == (sourceTransposeB.drop 184).take 8) = true := by
  decide +kernel

private theorem rightMask023 :
    (rightGaps023.map gapMask == (quotientTransposeRows.drop 184).take 8) = true := by
  decide +kernel

private theorem products023 :
    (leftGaps023.map (gapRow quotientTransposeRows) == rightGaps023.map (gapRow targetB)) = true := by
  decide +kernel

theorem block023 :
    checkEqualProducts quotientTransposeRows targetB
      ((sourceTransposeB.drop 184).take 8) ((quotientTransposeRows.drop 184).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask023) (beq_iff_eq.mp rightMask023)
    (beq_iff_eq.mp products023)

end QuotientGeneratorBChecks
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
