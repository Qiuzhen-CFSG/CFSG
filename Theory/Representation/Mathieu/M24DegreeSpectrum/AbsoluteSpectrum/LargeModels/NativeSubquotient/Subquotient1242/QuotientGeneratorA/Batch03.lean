module
public meta import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.GapLiteral
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.QuotientGeneratorA.Batch02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242.Matrices

/-!
# Literal quotientGeneratorA matrix identity

Separate mask and product checks run in bounded sequential batches.
The saved witness is unchanged; see source/README.md for provenance.
-/

set_option Elab.async false
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
open Degree220Pair.NativeActions.CertificatePacked Packed
open Degree320Pair.MatrixCertificates.TraceRows

namespace QuotientGeneratorAChecks

private noncomputable def left024Row0Part0 : List ℕ := native_gaps% "2,2,0,0,0,0,2,1,0,1,0,0,1,6,0,1,0,0,3,2,1,0,3,0,1,3,3,2,0,0,0,1,0,5,0,2,0,0,1,1,5,1,0,0,1,0,0,2,1,2,1,1,1,0,2,0,0,0,1,0,0,0,0,0,0,2,0,0,0,0,0,4,0,1,1,0,2,0,1,2,1,0,0,0,1,0,1,0,1,0,0,0,2,0,0,0,2,0,2,1,3,0,0,0,1,0,0,2,0,2,1,0,0,3,0,6,0,0,3,0,0,3" [[]]

private noncomputable def left024Row0 : List ℕ := left024Row0Part0

private noncomputable def left024Row1Part0 : List ℕ := native_gaps% "2,1,5,0,2,0,0,2,4,0,2,5,2,0,1,1,3,2,6,1,0,0,1,0,1,0,0,0,0,1,0,4,1,1,1,3,0,0,2,6,2,1,0,0,0,0,0,0,1,4,0,0,0,2,1,0,1,0,0,0,0,0,0,2,0,0,0,0,0,1,1,1,3,1,4,1,0,0,1,4,0,4,0,0,2,1,2,0,0,2,0,3,1,0,3,1,0,0,0,3,3,0,1,1,0,0,2,0" [[]]

private noncomputable def left024Row1 : List ℕ := left024Row1Part0

private noncomputable def left024Row2Part0 : List ℕ := native_gaps% "0,0,1,0,0,0,0,1,0,1,0,2,1,0,3,1,3,2,0,3,0,0,0,3,1,0,0,1,0,1,2,3,3,0,0,0,0,1,0,0,1,0,3,0,1,1,6,1,1,1,0,0,2,0,0,1,1,0,3,1,0,1,2,1,0,0,0,0,2,0,1,1,2,0,0,0,0,3,0,1,2,0,0,1,0,0,0,6,0,1,3,0,0,0,0,0,1,0,0,5,1,0,0,2,0,0,1,1,0,0,0,1,0,1,0,0,4,0,2,0,0,0,1,4,0" [[]]

private noncomputable def left024Row2 : List ℕ := left024Row2Part0

private noncomputable def left024Row3Part0 : List ℕ := native_gaps% "1,0,3,0,6,1,0,1,3,4,1,0,2,0,2,0,0,0,0,0,1,0,2,0,1,1,1,0,0,0,0,1,0,0,0,0,1,1,1,5,0,5,2,3,1,0,2,0,0,3,3,0,0,0,0,0,0,0,0,1,0,0,1,1,2,0,0,3,2,2,0,0,0,1,0,0,1,4,1,1,2,0,0,0,0,0,0,3,1,0,0,2,1,0,0,3,0,2,0,0,1,0,0,2,2,1,3,0,0,1,1,0,0,1,0,0,1,0,1,0,0,3,0" [[]]

private noncomputable def left024Row3 : List ℕ := left024Row3Part0

private noncomputable def left024Row4Part0 : List ℕ := native_gaps% "0,0,0,1,2,3,3,0,0,1,3,1,1,0,0,0,0,0,1,0,0,7,0,3,0,0,1,0,0,1,0,0,0,2,1,1,0,0,1,0,1,0,0,1,0,1,0,0,2,0,0,1,3,0,1,0,0,0,1,0,1,0,0,1,3,0,1,0,2,1,0,0,1,1,1,3,2,5,0,1,0,0,0,2,0,0,0,3,0,0,0,0,2,5,0,4,1,0,2,0,2,0,4,7,1,0,4,0,0,1,1,0,0,0,1,0,0,1,1,3" [[]]

private noncomputable def left024Row4 : List ℕ := left024Row4Part0

private noncomputable def left024Row5Part0 : List ℕ := native_gaps% "11,0,4,3,1,3,2,2,0,0,0,0,0,0,3,3,0,0,1,5,2,1,0,0,0,1,1,1,1,2,0,0,2,3,0,0,0,5,1,0,0,0,1,2,1,2,1,1,0,0,0,1,4,2,0,1,1,2,3,2,6,1,1,2,2,5,1,0,1,1,0,0,2,2,1,1,0,3,0,0,3,1,1,0,0,1,1,0,1,2,0,3,0,1,2,0,0,0,1,3,0" [[]]

private noncomputable def left024Row5 : List ℕ := left024Row5Part0

private noncomputable def left024Row6Part0 : List ℕ := native_gaps% "2,6,0,3,1,1,0,0,3,2,0,0,0,3,0,4,0,0,0,4,0,0,3,1,2,2,1,6,0,0,1,0,0,2,1,3,0,0,4,0,0,0,1,2,0,0,0,0,0,0,4,2,2,0,0,1,0,0,3,0,2,1,0,1,0,0,1,1,2,0,0,0,0,0,0,5,0,0,0,2,0,0,0,0,0,0,4,0,0,0,2,7,0,0,2,0,1,0,0,1,2,0,0,1,1,7,0,0,0,0,0,1,4,0" [[]]

private noncomputable def left024Row6 : List ℕ := left024Row6Part0

private noncomputable def left024Row7Part0 : List ℕ := native_gaps% "2,2,2,5,0,0,0,0,0,1,2,0,0,0,0,0,2,4,1,0,0,0,2,4,1,0,2,2,0,0,1,0,1,0,1,2,0,2,1,4,2,2,0,3,1,0,1,3,0,0,1,1,1,1,0,4,0,0,0,0,0,0,1,0,1,0,0,1,2,0,1,1,1,1,1,0,1,0,1,2,2,0,0,0,0,0,2,1,1,2,0,0,0,1,0,0,0,7,1,2,1,2,0,1,0,4,0,5,0,2,0,0,0,1,0,0,1" [[]]

private noncomputable def left024Row7 : List ℕ := left024Row7Part0

private noncomputable def leftGaps024 : List (List ℕ) := [left024Row0, left024Row1, left024Row2, left024Row3, left024Row4, left024Row5, left024Row6, left024Row7]

private noncomputable def right024Row0 : List ℕ := []

private noncomputable def right024Row1 : List ℕ := []

private noncomputable def right024Row2 : List ℕ := []

private noncomputable def right024Row3 : List ℕ := []

private noncomputable def right024Row4 : List ℕ := []

private noncomputable def right024Row5 : List ℕ := []

private noncomputable def right024Row6 : List ℕ := []

private noncomputable def right024Row7 : List ℕ := []

private noncomputable def rightGaps024 : List (List ℕ) := [right024Row0, right024Row1, right024Row2, right024Row3, right024Row4, right024Row5, right024Row6, right024Row7]

private theorem leftMask024 :
    (leftGaps024.map gapMask == (sourceTransposeA.drop 192).take 8) = true := by
  decide +kernel

private theorem rightMask024 :
    (rightGaps024.map gapMask == (quotientTransposeRows.drop 192).take 8) = true := by
  decide +kernel

private theorem products024 :
    (leftGaps024.map (gapRow quotientTransposeRows) == rightGaps024.map (gapRow targetA)) = true := by
  decide +kernel

theorem block024 :
    checkEqualProducts quotientTransposeRows targetA
      ((sourceTransposeA.drop 192).take 8) ((quotientTransposeRows.drop 192).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask024) (beq_iff_eq.mp rightMask024)
    (beq_iff_eq.mp products024)

private noncomputable def left025Row0Part0 : List ℕ := native_gaps% "1,3,0,0,2,0,1,0,1,2,0,0,1,1,5,3,0,1,0,0,3,0,0,0,2,0,3,2,0,2,0,1,0,2,0,0,2,0,7,0,6,2,0,1,0,0,0,0,1,0,2,1,2,0,6,0,0,1,1,0,3,2,0,0,3,1,1,0,0,1,1,0,1,0,2,1,0,2,2,3,0,0,0,1,1,1,0,2,1,0,3,2,0,0,1,1,1,0,3,0,0,1,2,0,0,0,3,1,0,1,0,1,0,0,0" [[]]

private noncomputable def left025Row0 : List ℕ := left025Row0Part0

private noncomputable def left025Row1Part0 : List ℕ := native_gaps% "0,0,0,0,4,2,3,1,1,0,0,3,1,0,0,1,0,5,1,0,3,0,1,0,0,0,2,2,0,1,0,0,0,0,1,0,3,0,0,2,1,2,1,0,0,1,1,1,0,0,2,1,3,0,1,0,2,1,0,0,3,0,2,0,0,1,6,2,0,0,0,0,5,3,0,4,1,0,1,0,0,5,0,1,0,0,0,0,0,0,6,0,0,3,0,0,1,0,1,0,4,1,0,2,0,0,1,0,2,2,0,0,0,0,2,0,0" [[]]

private noncomputable def left025Row1 : List ℕ := left025Row1Part0

private noncomputable def left025Row2Part0 : List ℕ := native_gaps% "2,0,0,5,3,0,0,1,0,3,1,0,1,1,0,0,0,0,0,2,2,2,1,3,0,4,3,0,1,0,0,2,1,1,0,1,3,4,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,2,2,0,3,2,3,0,4,1,0,0,2,0,0,0,0,2,2,0,1,0,1,6,2,2,1,2,0,0,2,0,2,0,0,0,0,0,0,1,0,1,1,0,0,3,0,2,0,0,2,0,0,0,0,0,0,4,1,2,0,0,0,0,0,0,0,0" [[]]

private noncomputable def left025Row2 : List ℕ := left025Row2Part0

private noncomputable def left025Row3Part0 : List ℕ := native_gaps% "0,2,0,0,0,1,0,0,0,3,0,0,1,0,0,0,0,0,2,3,2,0,0,0,0,0,3,0,1,0,1,0,1,0,1,0,0,0,8,1,3,6,3,1,1,1,1,0,0,1,1,0,0,1,1,2,0,1,1,0,1,1,1,2,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,1,3,0,0,2,1,0,0,1,0,0,0,0,2,0,4,0,0,4,1,0,1,0,0,0,0,0,0,1,0,0,1,0,2,0,2,1,0,0,0,3,2,1,3,6,0,1" [[]]

private noncomputable def left025Row3 : List ℕ := left025Row3Part0

private noncomputable def left025Row4Part0 : List ℕ := native_gaps% "1,0,2,0,0,2,0,0,9,0,1,0,0,0,0,2,4,1,1,1,0,1,1,4,0,2,2,0,1,0,0,0,0,2,1,0,0,1,0,0,1,2,0,1,0,2,2,2,0,1,0,0,0,1,0,3,2,2,0,0,6,0,0,1,0,0,4,1,0,0,0,0,1,2,0,2,0,1,0,1,4,4,0,0,1,1,2,0,1,0,0,0,0,1,1,0,0,0,2,4,4,0,3,3,2,0,2,3,0,7" [[]]

private noncomputable def left025Row4 : List ℕ := left025Row4Part0

private noncomputable def left025Row5Part0 : List ℕ := native_gaps% "0,1,0,1,0,0,1,2,1,0,1,1,0,1,2,4,1,0,0,2,0,0,0,0,4,1,2,0,3,0,0,3,2,0,0,7,1,4,0,0,1,4,0,2,0,0,0,1,0,0,2,0,1,1,0,1,5,0,0,4,0,0,1,1,1,1,1,0,5,2,0,0,1,1,0,1,0,0,2,3,0,0,1,7,0,3,0,0,2,0,1,1,2,2,0,3,0,1,4,0,0,1,2,0,3,0,3,1" [[]]

private noncomputable def left025Row5 : List ℕ := left025Row5Part0

private noncomputable def left025Row6Part0 : List ℕ := native_gaps% "1,1,0,1,1,4,3,2,0,2,3,1,1,0,2,2,2,3,0,1,0,0,0,0,1,13,1,3,0,1,0,5,1,5,1,0,0,2,3,0,4,5,0,0,3,1,0,1,0,0,1,0,2,1,0,1,8,0,0,6,0,1,0,2,0,4,3,0,0,1,1,1,0,1,0,1,0,3,2,1,2,3,1,0,0,1,0,0,0,3,1,0,0,0,4,1" [[]]

private noncomputable def left025Row6 : List ℕ := left025Row6Part0

private noncomputable def left025Row7Part0 : List ℕ := native_gaps% "2,0,1,1,0,5,0,1,1,0,1,0,0,1,0,0,1,0,1,0,0,0,1,0,2,1,3,0,0,3,2,0,2,4,0,2,0,0,1,0,0,0,0,0,3,2,2,1,0,0,3,0,0,0,0,0,1,0,1,0,0,2,0,0,0,2,1,5,0,5,4,0,0,1,0,0,2,1,2,3,0,1,1,0,0,2,0,0,0,0,1,1,0,0,2,0,1,0,0,0,3,0,0,1,1,0,0,2,4,0,3,1,1,0,0,1,1,3,1,0,0,1,0" [[]]

private noncomputable def left025Row7 : List ℕ := left025Row7Part0

private noncomputable def leftGaps025 : List (List ℕ) := [left025Row0, left025Row1, left025Row2, left025Row3, left025Row4, left025Row5, left025Row6, left025Row7]

private noncomputable def right025Row0 : List ℕ := []

private noncomputable def right025Row1 : List ℕ := []

private noncomputable def right025Row2 : List ℕ := []

private noncomputable def right025Row3 : List ℕ := []

private noncomputable def right025Row4 : List ℕ := []

private noncomputable def right025Row5 : List ℕ := []

private noncomputable def right025Row6 : List ℕ := []

private noncomputable def right025Row7 : List ℕ := []

private noncomputable def rightGaps025 : List (List ℕ) := [right025Row0, right025Row1, right025Row2, right025Row3, right025Row4, right025Row5, right025Row6, right025Row7]

private theorem leftMask025 :
    (leftGaps025.map gapMask == (sourceTransposeA.drop 200).take 8) = true := by
  decide +kernel

private theorem rightMask025 :
    (rightGaps025.map gapMask == (quotientTransposeRows.drop 200).take 8) = true := by
  decide +kernel

private theorem products025 :
    (leftGaps025.map (gapRow quotientTransposeRows) == rightGaps025.map (gapRow targetA)) = true := by
  decide +kernel

theorem block025 :
    checkEqualProducts quotientTransposeRows targetA
      ((sourceTransposeA.drop 200).take 8) ((quotientTransposeRows.drop 200).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask025) (beq_iff_eq.mp rightMask025)
    (beq_iff_eq.mp products025)

private noncomputable def left026Row0Part0 : List ℕ := native_gaps% "2,4,1,0,0,0,3,0,1,0,0,0,0,0,3,0,0,4,0,1,0,0,1,1,0,0,0,1,0,1,1,2,0,0,0,0,1,1,3,0,4,0,0,3,0,0,0,0,2,1,0,0,0,1,0,0,0,1,2,0,0,1,0,0,0,1,1,1,0,0,4,0,2,0,2,4,1,1,0,1,1,0,5,0,0,3,1,1,3,0,0,0,2,0,0,3,5,2,0,1,0,2,2,0,0,1,0,0,1,2,0,3,2,0,0,1,1,2,2,0,1" [[]]

private noncomputable def left026Row0 : List ℕ := left026Row0Part0

private noncomputable def left026Row1Part0 : List ℕ := native_gaps% "0,0,2,0,1,2,1,2,0,2,0,1,1,1,1,1,1,6,0,0,0,0,0,1,0,0,1,2,0,4,0,0,1,0,0,2,0,0,0,5,1,1,1,0,0,2,2,0,2,1,0,3,0,3,0,1,0,0,0,2,2,0,1,0,1,2,1,3,1,1,1,1,0,0,1,0,1,2,6,0,0,0,2,1,1,0,1,1,0,0,0,2,2,1,4,0,5,0,5,2,0,0,0,0,2,2,0,3,0,2,2,0,0" [[]]

private noncomputable def left026Row1 : List ℕ := left026Row1Part0

private noncomputable def left026Row2Part0 : List ℕ := native_gaps% "2,2,2,11,2,0,0,0,0,3,0,0,0,0,0,1,0,0,0,0,2,2,2,0,0,0,0,0,0,0,2,0,0,4,2,0,2,0,0,0,2,0,2,0,0,2,0,0,1,8,0,0,0,0,2,0,0,0,0,0,1,1,0,2,3,0,2,0,3,4,0,0,1,0,1,1,7,1,1,1,0,0,0,0,0,0,1,0,0,0,0,1,2,3,0,1,2,0,1,0,1,2,0,0,3,0,0,5,0,6,3,0" [[]]

private noncomputable def left026Row2 : List ℕ := left026Row2Part0

private noncomputable def left026Row3Part0 : List ℕ := native_gaps% "0,0,1,0,2,0,0,0,2,0,0,3,1,1,1,0,1,0,0,1,0,1,3,0,2,2,0,5,1,4,0,0,0,2,0,0,0,0,2,0,0,0,2,0,1,0,1,0,0,1,3,2,0,0,2,1,1,0,3,2,1,1,1,0,2,1,1,0,0,1,0,1,0,3,0,2,2,0,0,0,1,1,3,0,3,3,2,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,7,0,0,2,1,2,0,3,0,2,3,0,0,1,0,2,2" [[]]

private noncomputable def left026Row3 : List ℕ := left026Row3Part0

private noncomputable def left026Row4Part0 : List ℕ := native_gaps% "0,1,1,0,1,0,0,0,0,8,0,2,1,1,3,0,0,0,1,1,3,1,1,1,0,0,0,2,1,0,0,6,0,1,2,1,0,0,3,2,0,1,0,1,0,0,4,0,0,0,0,0,0,0,1,0,2,2,2,0,0,0,0,0,2,1,1,0,4,0,1,0,0,0,0,0,1,2,0,0,1,0,0,2,2,0,1,2,1,1,1,6,2,3,2,0,3,0,2,0,0,1,0,2,0,1,1,4,0,1,1,1,0,3,0" [[]]

private noncomputable def left026Row4 : List ℕ := left026Row4Part0

private noncomputable def left026Row5Part0 : List ℕ := native_gaps% "0,0,1,2,1,3,0,0,2,3,0,3,0,2,1,2,0,0,3,0,1,0,0,0,1,0,1,0,1,1,0,1,1,0,3,0,0,2,0,0,1,1,0,0,0,1,1,2,3,0,1,1,2,0,1,1,0,0,0,3,1,2,2,1,1,0,0,0,0,1,0,2,2,0,0,0,1,4,0,0,3,1,0,0,1,0,1,0,0,0,1,1,0,4,0,1,0,5,0,0,0,0,0,0,0,1,5,0,0,0,6,1,0,3,4,1,0" [[]]

private noncomputable def left026Row5 : List ℕ := left026Row5Part0

private noncomputable def left026Row6Part0 : List ℕ := native_gaps% "0,5,1,2,1,1,0,0,2,6,3,0,3,0,0,0,2,1,1,1,1,0,1,0,2,1,2,0,1,2,2,0,0,0,0,0,0,0,0,7,2,0,0,0,1,0,1,0,0,1,0,1,1,0,1,1,0,0,5,0,0,0,0,0,2,0,0,0,0,0,0,2,1,0,0,1,0,7,1,3,1,5,0,0,0,0,1,0,2,1,1,0,0,0,0,1,0,1,0,3,0,0,0,0,0,0,0,0,2,0,0,1,3,0,3,6,0" [[]]

private noncomputable def left026Row6 : List ℕ := left026Row6Part0

private noncomputable def left026Row7Part0 : List ℕ := native_gaps% "0,0,0,3,0,0,1,3,0,2,6,2,4,3,1,3,0,0,3,0,1,5,0,0,0,1,2,0,1,1,0,0,0,0,0,2,2,1,0,0,1,1,0,0,0,3,0,0,0,0,0,0,0,7,0,0,0,0,0,2,0,1,0,2,0,1,3,7,4,0,5,1,0,8,1,0,3,6,0,0,1,1,0,0,0,0,4,0,0,0,3,2,0,0,0,0,0,3,0,0,3,5,0,0" [[]]

private noncomputable def left026Row7 : List ℕ := left026Row7Part0

private noncomputable def leftGaps026 : List (List ℕ) := [left026Row0, left026Row1, left026Row2, left026Row3, left026Row4, left026Row5, left026Row6, left026Row7]

private noncomputable def right026Row0 : List ℕ := []

private noncomputable def right026Row1 : List ℕ := []

private noncomputable def right026Row2 : List ℕ := []

private noncomputable def right026Row3 : List ℕ := []

private noncomputable def right026Row4 : List ℕ := []

private noncomputable def right026Row5 : List ℕ := []

private noncomputable def right026Row6 : List ℕ := []

private noncomputable def right026Row7 : List ℕ := []

private noncomputable def rightGaps026 : List (List ℕ) := [right026Row0, right026Row1, right026Row2, right026Row3, right026Row4, right026Row5, right026Row6, right026Row7]

private theorem leftMask026 :
    (leftGaps026.map gapMask == (sourceTransposeA.drop 208).take 8) = true := by
  decide +kernel

private theorem rightMask026 :
    (rightGaps026.map gapMask == (quotientTransposeRows.drop 208).take 8) = true := by
  decide +kernel

private theorem products026 :
    (leftGaps026.map (gapRow quotientTransposeRows) == rightGaps026.map (gapRow targetA)) = true := by
  decide +kernel

theorem block026 :
    checkEqualProducts quotientTransposeRows targetA
      ((sourceTransposeA.drop 208).take 8) ((quotientTransposeRows.drop 208).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask026) (beq_iff_eq.mp rightMask026)
    (beq_iff_eq.mp products026)

private noncomputable def left027Row0Part0 : List ℕ := native_gaps% "0,2,3,0,0,1,1,0,0,1,0,3,2,1,1,1,1,0,0,0,2,0,3,0,2,0,0,2,1,0,0,2,0,1,2,13,0,3,3,1,0,2,0,1,1,1,4,3,1,1,0,4,1,0,3,0,1,0,0,0,1,0,4,0,0,0,1,1,0,0,0,1,2,0,1,1,1,0,3,0,1,1,1,3,1,0,0,0,2,0,1,1,0,0,1,0,0,0,2,0,0,4,2,1,0,0,0,2,0,2,1,0,0" [[]]

private noncomputable def left027Row0 : List ℕ := left027Row0Part0

private noncomputable def left027Row1Part0 : List ℕ := native_gaps% "3,0,0,0,0,1,0,5,4,0,3,0,1,2,3,2,1,0,1,1,0,0,0,0,0,0,4,2,2,0,0,2,0,2,0,0,0,0,1,1,0,0,2,1,0,1,2,1,0,0,4,0,1,3,0,1,2,1,0,0,0,0,1,0,0,0,0,1,0,0,7,1,1,0,1,0,1,1,2,0,2,0,0,4,0,0,5,0,1,0,1,2,0,1,1,0,3,4,1,0,0,2,2,1,0,0,0,0,1,0,0,4,0,0,0,1,0,0" [[]]

private noncomputable def left027Row1 : List ℕ := left027Row1Part0

private noncomputable def left027Row2Part0 : List ℕ := native_gaps% "4,1,1,2,1,1,0,2,0,0,0,0,6,0,2,2,1,0,1,0,0,2,2,0,0,1,0,2,0,0,0,1,0,6,0,1,0,2,0,1,0,2,0,1,0,1,0,0,0,0,3,0,2,2,1,1,2,0,1,1,1,1,2,0,0,0,0,6,0,1,1,2,0,3,2,2,2,1,0,0,1,0,0,0,1,2,3,3,3,0,0,0,1,3,0,0,1,1,4,5,0,0,3,4,0,0,0,3,0" [[]]

private noncomputable def left027Row2 : List ℕ := left027Row2Part0

private noncomputable def left027Row3Part0 : List ℕ := native_gaps% "1,3,1,4,1,0,1,0,0,0,2,0,0,0,1,2,3,0,0,3,0,4,1,0,4,1,0,0,2,1,2,0,0,0,1,3,1,2,4,0,0,1,0,1,0,0,1,0,0,0,3,3,0,0,0,0,3,2,0,0,0,2,0,0,0,3,1,0,0,1,0,1,1,0,0,0,1,0,1,0,0,3,1,0,0,0,0,1,0,1,0,0,0,6,0,1,3,0,0,7,4,4,0,0,7,0,1,1,0,5,0" [[]]

private noncomputable def left027Row3 : List ℕ := left027Row3Part0

private noncomputable def left027Row4Part0 : List ℕ := native_gaps% "5,0,3,2,0,3,0,1,0,0,0,0,4,0,5,0,0,1,2,0,1,2,1,0,2,0,1,1,1,0,2,2,0,4,1,0,0,0,1,1,1,0,0,1,1,1,0,0,0,0,0,0,0,1,1,0,0,1,1,0,0,0,0,2,11,4,3,0,1,0,0,0,0,4,1,0,0,0,1,1,1,1,0,0,0,1,1,0,0,3,0,4,0,0,0,0,1,0,5,1,0,0,1,1,1,0,0,1,1,1,3,1,0,0,1,1,1" [[]]

private noncomputable def left027Row4 : List ℕ := left027Row4Part0

private noncomputable def left027Row5Part0 : List ℕ := native_gaps% "0,1,1,3,2,3,0,4,0,1,2,0,0,0,3,0,0,1,0,0,2,1,0,0,3,0,3,0,2,6,2,0,6,0,0,0,0,1,0,5,0,0,1,0,1,2,0,0,0,5,0,1,1,2,0,0,0,1,0,0,0,0,5,0,3,1,0,0,0,4,0,0,5,0,3,1,1,0,0,1,0,0,0,1,4,0,2,0,5,2,0,0,5,1,0,1,3,0,0,1,0,2,2,1,0,1,0,1" [[]]

private noncomputable def left027Row5 : List ℕ := left027Row5Part0

private noncomputable def left027Row6Part0 : List ℕ := native_gaps% "1,1,5,0,0,10,2,0,0,1,2,0,0,0,2,0,3,3,1,3,0,1,0,0,0,0,4,0,6,1,1,1,2,0,2,2,5,0,0,1,1,0,6,1,2,1,0,1,1,0,1,0,0,0,0,0,3,0,3,1,0,0,0,0,0,0,0,0,0,1,0,0,0,1,1,0,0,0,1,0,0,0,1,2,0,2,0,0,4,0,1,0,0,0,0,2,1,4,1,0,1,1,0,1,0,0,1,5,0,2,1" [[]]

private noncomputable def left027Row6 : List ℕ := left027Row6Part0

private noncomputable def left027Row7Part0 : List ℕ := native_gaps% "1,0,0,1,0,0,0,0,2,8,2,6,0,1,1,3,0,0,1,1,0,0,2,0,0,1,1,0,0,5,0,0,6,0,5,0,2,0,1,0,4,0,0,5,1,1,0,0,0,4,3,0,1,5,1,4,2,3,3,0,3,1,0,1,0,1,0,0,4,0,0,0,1,4,0,0,1,3,0,2,2,0,0,2,1,2,1,1,2,0,0,1,0,3,1,1,0,0,0,0,3,0" [[]]

private noncomputable def left027Row7 : List ℕ := left027Row7Part0

private noncomputable def leftGaps027 : List (List ℕ) := [left027Row0, left027Row1, left027Row2, left027Row3, left027Row4, left027Row5, left027Row6, left027Row7]

private noncomputable def right027Row0 : List ℕ := []

private noncomputable def right027Row1 : List ℕ := []

private noncomputable def right027Row2 : List ℕ := []

private noncomputable def right027Row3 : List ℕ := []

private noncomputable def right027Row4 : List ℕ := []

private noncomputable def right027Row5 : List ℕ := []

private noncomputable def right027Row6 : List ℕ := []

private noncomputable def right027Row7 : List ℕ := []

private noncomputable def rightGaps027 : List (List ℕ) := [right027Row0, right027Row1, right027Row2, right027Row3, right027Row4, right027Row5, right027Row6, right027Row7]

private theorem leftMask027 :
    (leftGaps027.map gapMask == (sourceTransposeA.drop 216).take 8) = true := by
  decide +kernel

private theorem rightMask027 :
    (rightGaps027.map gapMask == (quotientTransposeRows.drop 216).take 8) = true := by
  decide +kernel

private theorem products027 :
    (leftGaps027.map (gapRow quotientTransposeRows) == rightGaps027.map (gapRow targetA)) = true := by
  decide +kernel

theorem block027 :
    checkEqualProducts quotientTransposeRows targetA
      ((sourceTransposeA.drop 216).take 8) ((quotientTransposeRows.drop 216).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask027) (beq_iff_eq.mp rightMask027)
    (beq_iff_eq.mp products027)

private noncomputable def left028Row0Part0 : List ℕ := native_gaps% "1,5,0,3,0,1,0,1,2,0,0,1,0,0,0,2,0,0,2,1,0,0,2,0,0,2,2,2,3,1,1,1,1,1,0,1,0,1,1,0,1,0,1,2,0,2,0,3,0,1,0,1,3,4,0,0,0,0,0,1,1,1,4,1,1,0,0,2,0,0,0,2,1,0,0,3,1,5,1,2,1,0,1,0,0,2,1,1,0,1,0,0,0,2,1,0,0,1,1,2,1,0,2,0,2,0,0,0,0,0,0,3,0,0,0,2,0,0,3,0" [[]]

private noncomputable def left028Row0 : List ℕ := left028Row0Part0

private noncomputable def left028Row1Part0 : List ℕ := native_gaps% "5,2,4,0,0,0,1,0,1,1,0,0,1,3,0,1,0,0,0,3,1,0,2,0,0,0,4,0,0,0,2,2,0,0,0,0,0,3,0,0,3,1,0,2,0,1,0,2,1,0,0,0,4,4,0,0,0,3,0,0,0,1,5,0,0,0,0,0,3,2,3,3,0,3,1,0,1,0,1,0,0,2,1,1,1,0,1,0,2,3,2,3,0,0,0,0,0,1,1,0,4,1,2,0,0,0,0,0,1,0,1,1,0,1,0,0,1,0,1" [[]]

private noncomputable def left028Row1 : List ℕ := left028Row1Part0

private noncomputable def left028Row2Part0 : List ℕ := native_gaps% "0,1,0,2,2,1,1,0,1,1,2,0,0,1,0,0,1,0,2,4,0,2,1,0,0,1,0,0,1,1,0,0,1,0,0,0,0,3,0,2,0,1,1,0,1,0,4,2,0,0,1,0,0,0,0,2,1,2,2,1,0,0,1,0,1,1,0,7,1,0,0,0,2,1,0,0,1,3,1,0,2,2,1,0,4,0,3,1,5,5,0,2,6,1,2,0,2,0,1,0,1,0,0,0,1,3,0,0,0,2,0,0,3,0" [[]]

private noncomputable def left028Row2 : List ℕ := left028Row2Part0

private noncomputable def left028Row3Part0 : List ℕ := native_gaps% "1,0,1,2,4,1,1,0,4,0,0,1,0,2,3,0,0,0,2,1,0,2,2,0,0,0,0,5,0,0,1,0,0,0,0,1,0,1,2,0,0,0,0,0,1,0,0,1,1,0,1,0,2,1,1,1,0,1,0,0,0,0,5,0,0,0,1,1,1,0,4,2,2,0,2,0,0,4,0,0,0,0,2,1,0,0,3,1,2,1,3,2,2,3,0,1,0,0,4,0,0,0,0,0,0,0,0,0,1,3,5,1,0,0,1,1,0,2,1,0,0" [[]]

private noncomputable def left028Row3 : List ℕ := left028Row3Part0

private noncomputable def left028Row4Part0 : List ℕ := native_gaps% "0,1,0,0,0,1,0,1,1,1,0,0,0,0,1,0,0,0,0,0,0,0,0,3,1,3,1,0,0,0,0,1,3,0,0,2,0,1,0,2,0,0,2,0,2,2,0,0,2,0,0,4,0,0,1,0,0,0,2,1,0,0,3,0,1,2,2,0,1,1,0,1,1,0,0,0,1,2,0,0,1,0,1,3,2,0,0,0,0,4,3,1,0,1,0,0,5,1,0,2,0,0,0,0,0,1,0,1,1,2,0,0,2,0,0,4,0,1,0,1" [[]]

private noncomputable def left028Row4 : List ℕ := left028Row4Part0

private noncomputable def left028Row5Part0 : List ℕ := native_gaps% "2,0,0,0,1,3,1,2,0,1,2,1,0,0,0,2,0,0,0,4,1,0,1,0,1,0,0,4,1,1,1,3,0,1,0,0,1,1,1,0,1,3,2,0,5,1,0,0,0,1,0,0,3,0,0,0,2,0,1,1,2,0,0,1,5,0,2,0,0,3,2,1,0,2,1,2,1,0,2,0,0,2,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,1,0,2,0,0,3,2,1,0,2,2,1,0,1,0,1,2,0,4,0,1,1" [[]]

private noncomputable def left028Row5 : List ℕ := left028Row5Part0

private noncomputable def left028Row6Part0 : List ℕ := native_gaps% "3,0,1,0,0,0,2,3,1,0,0,3,0,0,1,1,0,0,1,0,0,2,0,3,1,0,0,0,1,1,0,0,1,0,5,0,0,6,0,0,3,1,2,0,0,2,1,1,1,0,0,1,1,4,0,1,3,0,1,1,0,2,1,2,0,3,3,0,0,0,2,0,1,0,2,2,2,1,1,1,1,1,4,2,1,0,1,0,1,0,0,0,0,0,2,3,0,0,0,2,0,1,0,3,0,2,0,1,0,0,1,4,0,1,0,0,0" [[]]

private noncomputable def left028Row6 : List ℕ := left028Row6Part0

private noncomputable def left028Row7Part0 : List ℕ := native_gaps% "1,0,0,1,0,1,1,0,1,0,0,0,3,2,2,1,0,2,0,0,0,0,0,0,3,4,0,0,0,3,0,2,0,0,0,2,0,0,0,0,0,1,1,0,0,3,1,2,0,0,2,0,0,3,0,0,3,0,1,0,0,3,0,0,2,0,0,0,2,0,1,1,1,0,3,0,1,0,1,1,0,1,0,0,0,6,2,0,1,0,1,0,1,0,2,0,1,1,0,1,2,0,0,1,4,0,1,0,1,1,0,1,0,0,0,2,0,0,0,0,4,0,1,1,1,4,0" [[]]

private noncomputable def left028Row7 : List ℕ := left028Row7Part0

private noncomputable def leftGaps028 : List (List ℕ) := [left028Row0, left028Row1, left028Row2, left028Row3, left028Row4, left028Row5, left028Row6, left028Row7]

private noncomputable def right028Row0 : List ℕ := []

private noncomputable def right028Row1 : List ℕ := []

private noncomputable def right028Row2 : List ℕ := []

private noncomputable def right028Row3 : List ℕ := []

private noncomputable def right028Row4 : List ℕ := []

private noncomputable def right028Row5 : List ℕ := []

private noncomputable def right028Row6 : List ℕ := []

private noncomputable def right028Row7 : List ℕ := []

private noncomputable def rightGaps028 : List (List ℕ) := [right028Row0, right028Row1, right028Row2, right028Row3, right028Row4, right028Row5, right028Row6, right028Row7]

private theorem leftMask028 :
    (leftGaps028.map gapMask == (sourceTransposeA.drop 224).take 8) = true := by
  decide +kernel

private theorem rightMask028 :
    (rightGaps028.map gapMask == (quotientTransposeRows.drop 224).take 8) = true := by
  decide +kernel

private theorem products028 :
    (leftGaps028.map (gapRow quotientTransposeRows) == rightGaps028.map (gapRow targetA)) = true := by
  decide +kernel

theorem block028 :
    checkEqualProducts quotientTransposeRows targetA
      ((sourceTransposeA.drop 224).take 8) ((quotientTransposeRows.drop 224).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask028) (beq_iff_eq.mp rightMask028)
    (beq_iff_eq.mp products028)

private noncomputable def left029Row0Part5 : List ℕ := native_gaps% "1,1,0,2,1,0,0,0,0,0,3,0,0,0,0,0,0,0,0,3,0,0,0,0,1,0,0,2,1,0,0,1,0,1,0,0,0,1,2,1,0,0,0,1,0,6" [[]]

private noncomputable def left029Row0Part4 : List ℕ := native_gaps% "0,0,0,0,0,0,2,0,0,1,0,6,2,1,7,0,0,1,0,1,3,0,0,0,1,0,1,1,1,0,1,2,0,0,2,0,2,1,0,3,0,1,0,2,1,1,1,0,0,0,0,0,0,1,0,1,0,0,1,0,1,0,0,2,7,0,5,3,1,0,0,0,2,2,0,3,0,0,0,0,0,0,2,1,0,4,0,4,1,1,0,0,0,2,0,3,0,1,0,1,3,3,0,0,0,0,2,4,2,0,0,0,0,1,0,0,1,0,0,2,5,0,0,2,0,1,1,1" [left029Row0Part5]

private noncomputable def left029Row0Part3 : List ℕ := native_gaps% "2,4,0,0,2,0,1,1,0,0,0,1,0,4,0,2,1,1,0,0,2,0,0,2,0,0,2,0,5,1,1,1,0,1,1,0,5,0,0,0,0,1,2,0,0,1,0,6,2,1,1,0,1,2,0,2,0,0,5,1,1,0,2,0,1,2,0,2,0,0,0,0,0,0,1,0,1,3,3,0,1,1,0,1,0,1,1,3,2,0,2,4,0,0,0,0,0,0,1,0,0,12,1,6,1,0,1,2,2,3,1,1,0,1,0,0,0,0,2,3,4,1,1,0,1,3,2,3" [left029Row0Part4]

private noncomputable def left029Row0Part2 : List ℕ := native_gaps% "4,0,2,1,0,1,0,0,1,0,0,1,0,3,0,1,0,1,2,0,0,2,1,1,1,1,0,1,1,0,2,2,0,0,0,0,1,3,0,0,1,0,0,2,0,1,1,0,0,1,2,0,4,0,1,1,1,1,1,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,1,1,0,0,0,1,0,1,0,1,0,0,1,1,0,1,0,0,1,0,1,2,0,0,1,0,0,0,0,0,0,1,1,1,1,4,3,3,1,2,0,0,3,0,1,1,3,1,0,1,1,0,0,0" [left029Row0Part3]

private noncomputable def left029Row0Part1 : List ℕ := native_gaps% "1,2,1,1,2,0,1,0,3,0,0,5,0,0,1,2,1,0,2,3,0,2,6,3,0,2,0,0,0,0,3,0,0,0,0,0,8,0,0,2,6,5,0,1,0,0,0,3,3,0,2,0,1,0,1,0,1,0,1,1,0,2,0,0,0,3,1,3,1,1,0,0,3,0,0,1,0,0,0,0,1,3,0,1,2,1,5,0,2,1,0,3,0,1,0,1,1,3,2,0,1,0,0,0,0,0,2,2,0,2,1,0,1,1,1,1,1,4,1,2,1,0,1,1,2,1,1,2" [left029Row0Part2]

private noncomputable def left029Row0Part0 : List ℕ := native_gaps% "1,3,1,3,1,2,1,0,1,0,1,0,1,0,2,0,0,1,1,2,0,0,0,2,0,0,1,0,0,1,0,2,1,2,0,0,1,0,2,0,2,0,1,1,1,0,2,1,2,0,0,2,2,3,3,2,1,0,0,0,0,0,5,0,1,0,1,77,2,18,1,0,2,0,0,1,0,1,0,3,0,1,0,2,0,1,7,0,0,2,3,0,0,8,1,2,1,2,4,0,1,0,9,1,2,0,4,2,0,0,3,1,2,3,0,0,0,1,0,2,1,0,0,8,2,0,1,1" [left029Row0Part1]

private noncomputable def left029Row0 : List ℕ := left029Row0Part0

private noncomputable def left029Row1Part5 : List ℕ := native_gaps% "0,0,0,0,3,2,0,0,0,0,3,0,3,2,0,1,0,0,2,1,0,0,1,0,0,0,0,1,1,2,0,0,0,1,1,1,1,1,0,1,0,0,3,0,0,2,0,0,1,0,3,0,0,1" [[]]

private noncomputable def left029Row1Part4 : List ℕ := native_gaps% "1,1,3,6,0,0,1,3,1,0,0,4,2,1,0,0,0,1,1,5,0,0,0,0,1,0,1,0,1,0,0,0,1,0,2,1,0,0,0,0,1,2,0,4,0,1,5,0,0,0,2,1,0,0,1,0,0,0,3,1,1,0,0,3,0,1,0,0,0,1,1,0,3,2,0,4,0,0,1,2,0,2,0,0,0,2,1,8,0,0,0,1,2,0,0,1,5,1,2,0,0,4,0,0,0,0,1,1,0,1,0,0,0,2,3,1,2,0,5,2,0,2,0,0,0,4,0,2" [left029Row1Part5]

private noncomputable def left029Row1Part3 : List ℕ := native_gaps% "0,0,0,0,0,0,2,0,0,2,0,0,2,0,0,1,0,0,1,0,1,6,0,4,2,1,1,1,0,0,0,0,1,2,0,0,1,1,0,0,1,1,0,0,4,0,1,5,0,1,0,0,0,2,1,0,3,0,1,0,1,6,0,1,1,1,2,1,0,2,0,1,1,0,0,0,0,1,2,0,0,1,0,2,0,0,2,0,3,0,3,1,1,0,1,0,3,0,0,0,0,3,6,1,1,0,2,0,3,1,1,1,1,1,1,0,0,1,2,0,0,0,0,3,0,1,0,2" [left029Row1Part4]

private noncomputable def left029Row1Part2 : List ℕ := native_gaps% "0,0,0,0,1,0,0,2,1,0,3,0,1,2,1,0,1,0,0,0,0,1,0,1,1,4,3,0,0,0,2,1,2,2,2,1,1,6,0,1,9,1,0,1,0,2,0,0,1,0,3,0,2,0,1,4,2,0,1,0,2,1,0,0,1,0,0,2,0,0,2,0,0,2,0,0,3,1,0,1,2,1,1,0,1,1,4,0,1,0,0,0,1,0,0,0,1,0,10,0,0,1,0,0,0,2,0,1,0,1,0,2,0,0,4,3,2,2,0,0,1,0,3,3,1,1,0,1" [left029Row1Part3]

private noncomputable def left029Row1Part1 : List ℕ := native_gaps% "0,1,0,2,3,0,1,0,2,0,3,1,1,2,3,1,0,1,0,0,4,0,0,1,2,1,1,0,0,0,2,3,0,1,0,3,2,0,0,1,1,4,1,4,2,2,1,2,0,2,0,3,0,0,0,1,2,0,0,1,0,1,1,3,0,0,1,1,0,0,0,2,2,2,0,0,0,1,2,1,2,0,1,1,2,0,2,1,4,2,1,1,0,2,2,0,0,0,1,0,0,4,0,1,0,1,2,0,2,1,3,0,1,0,0,1,0,0,0,2,1,9,0,0,0,0,1,1" [left029Row1Part2]

private noncomputable def left029Row1Part0 : List ℕ := native_gaps% "2,0,0,0,0,0,4,1,0,2,1,2,3,1,0,2,3,0,1,2,1,0,1,0,0,0,1,2,0,1,0,0,0,0,1,0,0,0,0,3,1,1,0,1,0,0,0,0,2,1,0,1,0,0,0,0,0,0,2,2,2,3,0,2,0,1,0,1,0,1,0,1,0,78,0,24,1,0,2,1,0,0,3,1,0,1,3,0,0,0,2,1,0,1,0,1,1,0,0,0,9,1,2,1,0,5,0,2,0,3,1,0,0,0,0,0,2,0,0,3,2,1,5,5,1,0,1,3" [left029Row1Part1]

private noncomputable def left029Row1 : List ℕ := left029Row1Part0

private noncomputable def left029Row2Part5 : List ℕ := native_gaps% "3,0,1,4,1,1,2,0,2,0,0,0,0,0,2,1,8,0,2,2,1,0,1,2,1,0,4,2,0,0,2,0,0,0,0,0,0,0,0,0,5,0,1,1,0,0,0,0,1,1,0,0,0,2,0,0,2,0,0,2,0" [[]]

private noncomputable def left029Row2Part4 : List ℕ := native_gaps% "0,1,1,1,0,1,2,2,0,0,0,0,1,0,0,4,0,0,0,0,0,0,1,0,2,2,1,0,0,0,0,2,0,0,1,2,1,0,0,1,2,3,1,0,3,0,0,1,4,0,1,0,2,2,0,0,1,4,2,1,0,5,2,1,1,0,2,7,1,1,3,0,0,0,1,4,0,1,0,1,3,1,0,0,0,0,0,3,3,0,0,0,0,1,1,0,2,1,1,0,0,3,1,2,1,0,0,4,1,0,0,4,0,0,4,0,1,0,0,2,3,0,3,0,0,0,1,0" [left029Row2Part5]

private noncomputable def left029Row2Part3 : List ℕ := native_gaps% "0,0,1,0,0,0,1,0,1,1,0,2,0,0,0,1,1,0,1,3,1,1,0,0,0,0,4,1,0,1,0,0,0,0,1,0,2,0,0,4,0,0,0,0,4,1,2,0,1,2,2,0,5,0,1,0,0,2,0,1,0,0,0,0,3,1,0,3,2,3,0,0,1,0,0,2,0,3,0,1,0,0,4,2,1,0,1,0,0,4,0,0,0,1,0,3,0,0,4,0,1,0,2,1,1,0,1,0,1,2,1,0,1,4,1,1,0,0,1,0,2,1,0,0,2,0,0,0" [left029Row2Part4]

private noncomputable def left029Row2Part2 : List ℕ := native_gaps% "0,0,0,1,0,3,2,1,0,0,0,0,1,0,3,1,2,3,1,0,0,2,0,0,3,2,0,6,0,0,0,1,1,0,0,0,0,0,0,0,1,1,3,0,0,0,1,0,1,1,2,5,0,0,0,0,0,0,0,0,1,2,1,1,2,2,1,2,0,0,0,1,0,1,0,1,6,0,0,2,0,4,2,0,0,3,0,0,0,0,2,2,0,1,1,2,1,3,1,1,0,2,5,0,2,0,4,2,0,1,1,1,0,0,1,0,1,0,0,3,0,0,0,1,2,0,1,7" [left029Row2Part3]

private noncomputable def left029Row2Part1 : List ℕ := native_gaps% "0,0,0,0,0,0,0,2,0,0,1,0,2,0,2,0,0,0,1,0,3,0,0,0,1,0,2,1,2,0,2,1,3,0,3,1,0,0,0,4,1,0,0,0,6,0,1,1,0,0,0,0,0,0,1,0,1,3,1,2,0,3,0,0,1,2,4,0,2,0,3,1,0,0,0,2,0,4,1,0,2,5,0,0,0,0,3,0,4,0,0,1,1,0,1,2,0,0,0,1,0,0,0,1,3,1,4,0,0,0,0,0,0,1,1,0,1,1,0,1,1,1,5,0,0,4,0,0" [left029Row2Part2]

private noncomputable def left029Row2Part0 : List ℕ := native_gaps% "0,0,1,1,2,0,0,0,1,0,1,0,2,3,0,1,0,0,0,2,1,3,2,1,0,1,2,1,1,0,0,0,0,1,1,0,2,2,0,1,0,3,0,0,0,1,2,0,2,0,0,0,0,3,4,1,2,0,1,2,0,0,1,1,0,4,0,3,77,1,18,0,1,2,0,1,0,0,1,0,0,1,1,2,1,0,3,0,0,1,1,2,2,0,0,0,0,0,0,4,8,2,0,0,2,1,0,2,3,4,0,4,0,0,1,1,0,6,0,1,1,1,7,4,2,0,0,0" [left029Row2Part1]

private noncomputable def left029Row2 : List ℕ := left029Row2Part0

private noncomputable def left029Row3Part5 : List ℕ := native_gaps% "0,2,0,0,0,3,0,0,3,0,0,3,3,1,0,0,1,0,2,1,0,1,0,2,1,0,1,1,0,4,0,1,1,4" [[]]

private noncomputable def left029Row3Part4 : List ℕ := native_gaps% "0,3,0,4,1,3,1,1,0,2,1,0,0,1,0,3,2,2,0,1,0,0,0,3,1,0,1,0,4,0,0,0,0,0,0,0,0,0,0,3,1,0,0,1,1,1,1,0,0,0,1,2,2,1,0,1,0,2,4,2,1,0,0,0,2,1,1,0,4,3,0,0,2,0,0,3,4,0,1,0,2,1,0,1,2,0,0,1,4,0,3,1,2,3,0,1,3,0,0,0,1,2,1,0,0,0,2,2,3,2,0,1,0,0,1,1,1,4,5,0,0,1,3,0,0,0,1,0" [left029Row3Part5]

private noncomputable def left029Row3Part3 : List ℕ := native_gaps% "0,1,0,0,2,0,0,3,3,1,0,0,0,4,0,0,0,1,3,2,2,1,2,1,0,2,0,0,0,0,0,0,0,2,0,0,2,1,2,0,1,2,0,0,4,2,0,4,3,1,0,0,0,4,0,0,2,0,0,1,0,0,0,1,0,0,1,2,2,0,1,1,0,1,2,0,0,5,1,1,0,2,0,0,1,0,0,1,2,0,1,0,0,2,0,0,0,2,0,0,1,1,0,0,0,4,0,0,0,4,2,2,0,0,2,3,0,0,0,1,2,5,0,5,0,0,2,0" [left029Row3Part4]

private noncomputable def left029Row3Part2 : List ℕ := native_gaps% "1,4,5,1,1,2,0,0,6,0,2,0,0,0,0,0,4,0,0,0,2,0,3,0,0,3,0,0,0,1,1,0,0,0,0,2,4,1,5,1,3,1,1,2,1,0,2,1,1,1,0,1,1,0,0,0,0,0,2,3,0,1,1,0,1,1,1,1,0,0,2,1,1,1,4,0,1,2,0,4,0,1,2,0,1,1,0,0,0,0,0,0,4,1,0,0,0,1,0,3,0,0,2,0,4,2,1,0,3,0,0,0,1,0,1,0,0,0,0,0,1,1,1,0,4,0,0,1" [left029Row3Part3]

private noncomputable def left029Row3Part1 : List ℕ := native_gaps% "4,2,1,1,2,5,1,4,2,0,3,1,0,1,1,1,0,0,0,3,0,0,1,4,0,0,3,1,1,3,2,0,5,0,1,3,1,0,0,1,0,1,2,0,5,2,0,1,2,1,1,0,0,0,2,2,0,0,1,0,1,1,1,0,2,0,1,3,0,0,0,1,1,0,0,3,0,1,0,5,0,1,1,1,2,0,0,0,0,2,1,1,0,2,1,0,0,1,0,1,0,1,0,2,0,4,1,0,0,6,0,4,1,1,4,1,0,0,1,0,2,1,0,1,0,0,0,0" [left029Row3Part2]

private noncomputable def left029Row3Part0 : List ℕ := native_gaps% "0,1,0,0,0,0,6,0,0,0,4,0,3,0,0,4,1,3,3,1,0,0,2,2,0,1,0,0,1,1,1,0,0,0,0,2,1,4,0,2,0,0,0,0,1,2,2,0,2,0,2,0,0,0,0,2,0,0,0,1,1,2,1,0,1,1,1,78,0,20,0,0,1,1,1,1,0,0,2,0,1,3,1,1,0,0,1,0,1,0,0,1,0,3,0,0,0,1,4,3,1,2,1,0,1,3,4,5,1,1,3,5,0,4,0,2,4,0,0,5,0,1,4,0,0,4,0,0" [left029Row3Part1]

private noncomputable def left029Row3 : List ℕ := left029Row3Part0

private noncomputable def left029Row4Part5 : List ℕ := native_gaps% "1,0,0,0,2,1,0,1,0,0,0,2,4,0,0,1,1,3,4,0,3,0,2,1,0,1,2,1,1,2,4,2,1,4,1,0,3,0,0,0,2,1,0,0,1,2,4,0,1,1,1,0,3,1,6,1,0,2,0,0,1,0,3,2,0,1,0" [[]]

private noncomputable def left029Row4Part4 : List ℕ := native_gaps% "2,0,2,4,1,0,0,1,4,3,2,0,0,1,0,0,0,1,0,0,2,1,4,1,3,1,0,0,0,0,0,2,0,1,2,2,6,2,2,3,0,0,1,1,1,1,0,1,0,1,0,0,1,0,2,2,2,1,1,2,2,0,1,0,1,0,0,3,2,0,1,0,3,0,0,2,0,1,1,1,0,0,4,1,0,0,3,1,2,0,0,1,0,1,0,0,0,0,2,0,1,3,1,0,1,0,0,3,0,0,0,2,2,2,0,4,0,0,0,1,1,0,0,0,0,0,0,0" [left029Row4Part5]

private noncomputable def left029Row4Part3 : List ℕ := native_gaps% "0,0,4,3,0,0,0,0,0,2,0,0,0,0,1,3,0,0,0,0,0,0,1,0,0,1,1,2,0,1,0,1,1,0,0,0,1,0,1,0,0,0,1,0,0,0,1,0,3,0,1,0,0,1,0,0,1,1,2,2,0,0,2,0,0,0,0,0,3,1,0,0,4,2,3,0,0,0,0,5,0,0,3,1,0,1,0,3,0,2,2,1,0,3,0,1,0,0,0,1,6,0,0,0,0,0,3,1,0,0,11,0,1,1,0,2,1,1,0,2,1,2,0,0,1,0,0,0" [left029Row4Part4]

private noncomputable def left029Row4Part2 : List ℕ := native_gaps% "2,0,1,0,1,1,0,1,0,2,0,0,1,1,0,2,0,1,0,3,0,0,3,3,0,0,3,1,0,2,2,0,0,1,6,0,3,0,1,2,1,0,2,0,1,0,0,0,4,0,0,3,3,2,3,1,3,1,0,1,0,0,1,0,0,0,1,0,1,2,2,0,0,0,0,3,2,0,1,4,0,0,0,1,0,2,1,0,0,4,1,0,0,0,0,1,2,0,1,3,0,1,1,0,1,0,0,1,0,1,3,1,0,1,0,2,1,5,0,0,3,1,0,2,1,2,2,2" [left029Row4Part3]

private noncomputable def left029Row4Part1 : List ℕ := native_gaps% "1,1,0,0,0,1,1,1,0,1,0,1,0,0,0,0,0,0,0,0,0,2,2,0,0,0,0,1,0,3,2,1,0,0,6,0,0,0,0,0,2,7,2,0,0,2,1,0,0,0,1,0,1,2,1,1,0,0,2,0,1,6,3,0,0,0,0,0,1,0,0,0,1,3,0,0,2,0,0,3,0,0,0,2,2,6,0,0,4,4,2,0,0,0,0,2,1,2,2,0,1,0,0,0,0,0,5,2,0,0,0,0,0,0,0,3,1,0,0,3,0,0,1,0,0,3,0,9" [left029Row4Part2]

private noncomputable def left029Row4Part0 : List ℕ := native_gaps% "2,0,0,0,1,0,0,0,0,0,0,1,0,0,0,1,3,1,1,0,0,0,1,2,1,1,0,4,0,1,0,2,2,0,1,1,0,1,1,0,0,0,0,0,1,0,0,0,0,0,0,2,0,0,1,0,1,0,0,1,0,0,0,0,2,1,0,2,1,0,0,1,0,1,0,0,0,2,0,0,0,0,0,0,1,77,1,22,0,5,1,0,3,3,0,0,0,0,0,0,0,0,1,0,0,7,5,0,3,0,1,0,1,3,3,2,1,0,1,4,2,1,1,3,3,1,1,1" [left029Row4Part1]

private noncomputable def left029Row4 : List ℕ := left029Row4Part0

private noncomputable def left029Row5Part5 : List ℕ := native_gaps% "0,1,1,0,3,0,0,0,3,0,2,1,5,2,0,2,1,2,0,1,1,1,0,2,0,1,0,1,0,1,0,1,0,1,2,0,1,1,4,2,0,1,0,0,0,2,2,2,0,0,1,1,1,0,0,1" [[]]

private noncomputable def left029Row5Part4 : List ℕ := native_gaps% "0,2,1,0,0,0,1,2,1,0,1,1,0,0,0,0,1,0,0,0,0,0,1,3,0,0,1,0,0,1,0,0,0,0,4,0,0,1,0,0,0,0,0,0,0,0,0,2,0,1,2,1,0,0,2,2,1,0,0,0,0,0,1,0,1,0,3,0,2,0,0,2,8,0,1,3,0,3,0,1,2,0,0,0,1,0,0,2,1,0,3,0,1,0,0,1,0,0,1,0,0,0,4,0,0,0,2,0,0,0,1,0,0,0,0,1,0,0,1,0,0,1,1,3,0,0,0,0" [left029Row5Part5]

private noncomputable def left029Row5Part3 : List ℕ := native_gaps% "0,1,7,6,1,0,1,11,0,4,4,7,0,0,2,6,0,0,0,1,4,2,0,1,0,0,3,1,5,1,1,1,1,0,0,1,1,2,1,0,0,1,0,0,3,0,1,0,0,0,2,1,0,1,1,2,0,2,0,3,0,2,3,0,0,0,2,0,2,1,3,0,0,3,1,1,3,7,0,0,0,1,2,2,0,0,0,0,1,2,1,1,1,0,2,0,0,0,1,0,5,1,1,0,0,0,0,0,0,0,0,3,2,1,0,0,1,2,1,2,0,0,5,0,0,0,0,0" [left029Row5Part4]

private noncomputable def left029Row5Part2 : List ℕ := native_gaps% "3,1,0,1,2,1,0,0,0,0,2,4,1,1,0,1,1,4,0,0,0,1,0,0,3,0,0,0,1,0,1,0,0,0,0,0,4,4,1,0,0,3,2,0,7,3,2,0,0,0,1,0,2,5,0,0,1,1,0,1,0,1,0,3,1,4,1,0,1,1,0,2,0,0,0,0,2,4,4,0,2,2,1,2,0,0,0,1,0,7,1,4,0,1,0,0,2,2,2,2,0,0,1,1,1,0,1,1,1,1,0,3,1,0,2,2,2,1,1,0,0,1,0,1,7,0,0,0" [left029Row5Part3]

private noncomputable def left029Row5Part1 : List ℕ := native_gaps% "2,1,1,1,0,0,3,0,1,0,0,2,1,0,2,1,0,0,2,1,1,1,0,0,0,1,2,0,0,0,0,1,1,1,0,5,0,0,0,1,1,1,1,0,2,2,1,1,2,2,2,0,0,0,3,0,0,0,1,2,0,1,0,6,10,0,2,0,0,0,0,3,1,0,1,3,1,0,2,1,0,1,1,0,0,1,2,0,4,0,0,0,1,0,0,2,0,0,2,1,0,0,1,0,0,2,0,0,0,0,4,6,1,1,0,3,1,0,1,1,0,0,3,1,0,1,1,0" [left029Row5Part2]

private noncomputable def left029Row5Part0 : List ℕ := native_gaps% "0,2,1,0,0,5,1,2,0,0,0,0,0,5,0,0,1,0,2,0,0,0,0,0,0,0,1,2,0,0,0,1,0,0,0,0,4,1,2,0,1,6,0,0,0,0,0,1,0,1,0,0,0,0,1,1,0,1,2,0,1,0,0,0,0,1,3,1,5,1,0,1,0,0,77,21,0,0,2,0,2,0,0,0,1,0,0,2,1,0,0,0,5,0,0,1,0,3,2,0,2,4,0,9,0,1,3,0,0,6,1,0,0,0,1,0,1,0,0,0,1,0,0,1,0,1,2,1" [left029Row5Part1]

private noncomputable def left029Row5 : List ℕ := left029Row5Part0

private noncomputable def left029Row6Part5 : List ℕ := native_gaps% "1,0,1,1,0,0,1,1,4,0,1,1,0,0,0,0,0,0,0,0,3,0,1,1,0,0,1,1,0,1,0,0,0,3,0,1,6,0,0,3" [[]]

private noncomputable def left029Row6Part4 : List ℕ := native_gaps% "1,1,0,5,1,0,0,4,1,0,1,1,0,2,2,0,0,0,1,0,0,5,1,0,0,0,2,0,3,0,0,1,0,1,0,2,0,0,1,0,0,0,5,3,1,4,0,0,1,0,0,0,5,1,1,1,2,0,2,6,2,0,1,2,0,2,0,1,1,1,1,0,0,2,0,1,0,0,1,2,1,2,0,3,0,0,0,2,0,1,4,0,0,0,2,2,1,0,1,0,0,0,4,0,0,0,1,0,2,0,7,0,0,5,5,3,2,0,0,4,0,0,0,0,3,0,0,0" [left029Row6Part5]

private noncomputable def left029Row6Part3 : List ℕ := native_gaps% "0,1,3,1,1,1,2,0,3,0,0,1,1,0,1,1,2,1,1,3,0,1,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,3,0,1,2,1,2,0,4,0,0,1,1,0,0,0,1,0,0,0,1,4,2,0,3,1,1,4,0,1,0,1,0,0,0,1,2,2,1,1,1,4,0,3,3,0,0,2,0,2,0,2,5,0,3,0,1,1,1,0,0,0,0,1,0,0,1,0,0,1,0,1,3,0,0,2,1,5,0,1,1,0,0,0,0,0,0,0,2,0,0" [left029Row6Part4]

private noncomputable def left029Row6Part2 : List ℕ := native_gaps% "0,1,0,2,1,1,0,0,0,2,0,0,0,1,0,1,0,1,0,0,0,1,2,0,0,0,0,0,1,0,2,0,0,0,0,4,4,0,2,0,3,0,1,2,7,0,1,1,1,3,0,0,0,3,0,0,1,3,0,1,2,0,1,0,3,2,0,3,0,0,2,0,1,0,6,2,0,0,0,2,2,4,0,0,7,0,0,0,4,3,4,0,1,0,1,0,3,1,1,2,0,1,1,1,1,0,1,1,0,0,2,0,0,0,0,0,0,0,0,0,0,2,3,3,2,0,2,0" [left029Row6Part3]

private noncomputable def left029Row6Part1 : List ℕ := native_gaps% "2,0,0,0,1,3,1,0,0,1,0,4,1,0,0,0,1,1,0,0,3,0,6,0,1,6,2,4,0,0,0,1,3,0,2,0,1,4,2,5,0,0,1,0,1,2,2,0,0,4,0,0,0,3,3,1,0,0,0,3,0,2,1,3,0,3,1,2,2,0,2,0,1,0,0,0,1,8,0,0,1,2,0,0,0,0,0,2,0,0,1,1,5,1,0,1,0,0,0,0,0,2,0,0,1,0,3,0,2,0,0,1,1,0,0,1,0,0,1,1,0,0,0,1,0,0,0,0" [left029Row6Part2]

private noncomputable def left029Row6Part0 : List ℕ := native_gaps% "0,4,0,1,1,1,4,0,4,1,0,1,0,2,1,3,0,0,0,1,0,0,2,0,2,0,0,1,1,2,0,1,1,1,0,4,1,1,4,1,0,3,0,0,0,1,0,0,1,5,3,2,1,3,1,0,5,0,80,20,1,0,3,3,1,1,1,1,3,5,0,1,0,0,2,0,2,4,0,4,1,0,1,4,1,3,1,0,6,1,0,0,0,1,0,0,0,0,0,0,1,0,0,2,0,0,0,2,0,0,0,0,1,0,8,0,0,0,4,1,0,3,1,1,0,1,1,0" [left029Row6Part1]

private noncomputable def left029Row6 : List ℕ := left029Row6Part0

private noncomputable def left029Row7Part5 : List ℕ := native_gaps% "0,0,1,0,0,0,3,3,2,1,0,1,0,2,1,1,2,4,0,0,2,1,5" [[]]

private noncomputable def left029Row7Part4 : List ℕ := native_gaps% "0,0,3,0,1,0,2,5,1,0,1,0,1,1,0,2,0,0,0,0,3,1,1,0,0,0,0,3,0,0,0,1,1,0,1,1,0,0,1,2,3,0,2,0,0,1,1,1,0,0,0,0,1,1,0,1,2,0,0,1,0,0,0,0,2,1,1,2,0,0,1,1,0,0,3,0,0,7,4,0,0,0,3,0,0,1,0,2,0,0,3,0,0,2,0,0,1,0,0,2,0,4,1,3,6,1,2,0,0,4,2,3,3,0,1,1,1,0,0,0,2,2,0,0,1,0,5,2" [left029Row7Part5]

private noncomputable def left029Row7Part3 : List ℕ := native_gaps% "0,0,0,2,4,1,2,0,0,3,1,0,1,1,0,0,1,0,0,4,0,2,0,1,0,0,2,1,0,1,0,1,2,0,0,1,3,1,0,3,0,0,0,1,1,2,0,0,5,2,3,0,2,0,1,1,0,0,0,2,1,1,4,0,0,2,3,5,2,0,0,0,0,0,3,0,0,0,2,1,0,3,0,3,0,1,0,0,0,1,1,0,2,0,1,0,0,0,1,0,1,0,0,2,0,5,1,0,1,2,0,1,0,1,0,7,5,1,2,1,3,0,2,0,1,0,1,1" [left029Row7Part4]

private noncomputable def left029Row7Part2 : List ℕ := native_gaps% "5,1,0,1,0,2,2,0,2,0,4,0,1,2,1,1,1,0,0,1,1,2,0,2,1,3,4,5,1,0,0,0,1,1,0,0,0,0,2,1,1,0,1,2,0,0,0,0,1,0,3,3,0,1,0,0,0,2,0,1,0,2,2,2,0,4,0,3,1,0,0,0,0,0,2,0,3,2,0,5,0,2,1,0,1,0,2,2,0,5,0,0,1,0,0,0,5,3,3,2,1,0,0,3,2,2,1,4,0,0,2,0,0,1,0,1,1,0,2,2,2,1,0,1,0,4,0,2" [left029Row7Part3]

private noncomputable def left029Row7Part1 : List ℕ := native_gaps% "1,4,3,1,0,0,1,0,1,5,0,1,1,2,0,2,0,0,0,2,1,0,7,2,0,2,1,0,3,0,0,4,1,0,1,2,0,1,1,0,0,0,1,0,0,2,0,0,1,3,1,1,2,0,0,5,0,0,0,0,3,1,2,0,0,0,0,0,0,0,2,2,1,4,0,0,0,0,2,1,0,1,2,7,2,2,0,0,0,1,2,0,0,1,1,0,1,0,1,4,1,0,1,2,1,0,0,0,0,1,1,3,0,0,0,1,1,1,2,0,4,0,1,1,0,0,0,0" [left029Row7Part2]

private noncomputable def left029Row7Part0 : List ℕ := native_gaps% "0,2,0,0,0,2,4,0,0,6,0,1,1,0,1,1,0,1,1,3,0,0,1,0,3,2,2,0,1,0,7,0,3,0,1,0,3,0,1,0,2,0,1,0,1,2,1,0,0,0,0,3,0,0,0,0,1,2,1,6,1,0,77,0,20,0,0,0,0,0,0,7,0,0,0,5,0,0,8,0,0,0,1,4,0,2,3,2,0,1,2,0,6,1,0,2,4,2,0,0,0,3,0,1,4,4,0,0,1,0,1,1,0,0,7,0,0,0,0,2,0,2,0,2,0,1,0,0" [left029Row7Part1]

private noncomputable def left029Row7 : List ℕ := left029Row7Part0

private noncomputable def leftGaps029 : List (List ℕ) := [left029Row0, left029Row1, left029Row2, left029Row3, left029Row4, left029Row5, left029Row6, left029Row7]

private noncomputable def right029Row0Part5 : List ℕ := native_gaps% "3,1,0" [[]]

private noncomputable def right029Row0Part4 : List ℕ := native_gaps% "1,0,1,0,2,0,0,0,0,0,0,0,1,2,1,1,1,2,1,3,2,1,0,0,3,1,0,0,0,0,0,7,0,0,0,3,0,0,0,5,0,1,0,2,2,0,3,0,0,1,2,1,0,3,4,0,0,0,0,2,0,1,0,4,2,0,1,0,0,0,0,3,0,0,0,1,1,1,0,2,1,1,7,1,0,0,0,4,0,0,1,0,0,0,1,4,0,2,3,2,1,0,2,1,0,0,0,0,0,2,3,3,4,1,0,0,0,0,2,0,0,1,0,0,2,2,0,0" [right029Row0Part5]

private noncomputable def right029Row0Part3 : List ℕ := native_gaps% "0,3,1,0,0,0,5,6,1,0,0,0,0,2,2,0,2,1,0,0,0,5,2,3,0,1,0,0,0,0,3,0,1,3,0,0,0,1,3,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,0,4,0,2,0,2,1,1,0,3,0,0,0,5,0,1,1,0,0,0,0,2,2,3,0,1,0,0,2,0,1,3,2,1,2,0,1,2,0,1,0,1,1,2,0,2,0,0,0,0,2,0,2,0,0,1,1,1,1,0,1,3,1,3,0,2,0,0" [right029Row0Part4]

private noncomputable def right029Row0Part2 : List ℕ := native_gaps% "0,0,3,4,0,1,0,2,4,0,0,2,0,2,3,0,0,3,1,0,2,1,0,2,0,0,0,3,0,1,1,3,0,1,0,6,1,0,0,0,0,0,0,1,0,0,1,1,3,1,0,0,0,1,1,2,2,0,0,0,0,0,1,1,1,0,0,1,0,0,0,1,0,1,1,3,0,2,0,0,1,0,0,1,1,2,0,2,3,0,0,3,2,1,3,0,0,4,2,0,1,1,0,1,3,2,0,0,1,4,1,0,2,0,1,0,1,0,1,0,0,1,0,4,0,0,0,1" [right029Row0Part3]

private noncomputable def right029Row0Part1 : List ℕ := native_gaps% "0,0,2,0,2,0,0,0,2,0,0,2,0,1,2,0,0,0,3,3,2,0,0,0,0,1,0,0,1,0,0,0,1,0,1,1,2,1,2,0,0,0,0,1,0,2,0,1,3,0,0,0,2,5,0,2,0,0,1,0,0,0,2,0,1,0,1,0,3,0,0,0,1,1,4,1,3,1,1,2,0,0,1,0,1,0,2,0,1,0,0,2,0,1,1,0,2,0,0,0,0,1,2,1,1,0,1,2,2,1,0,0,1,0,0,0,4,4,0,2,0,0,0,2,1,2,1,0" [right029Row0Part2]

private noncomputable def right029Row0Part0 : List ℕ := native_gaps% "0,0,0,0,0,1,8,1,0,3,0,0,1,1,2,1,1,0,2,1,0,1,0,2,0,0,2,0,0,1,0,0,2,0,0,2,2,0,0,1,0,0,1,1,1,1,3,3,0,0,1,1,2,1,0,0,0,0,3,1,0,0,4,1,4,0,0,0,0,2,1,1,0,2,0,2,1,6,3,2,0,0,1,2,0,5,2,0,0,1,0,0,1,2,0,0,1,2,1,0,0,0,0,2,1,1,2,0,1,0,0,3,1,0,2,1,0,0,0,0,2,0,0,0,0,1,0,5" [right029Row0Part1]

private noncomputable def right029Row0 : List ℕ := right029Row0Part0

private noncomputable def right029Row1Part4 : List ℕ := native_gaps% "0,0,0,0,0,0,0,0,2,0,2,1,1,0,2,0,0,0,0,0,1,2,0,0,1,0,0,1,1,0,0,0,0,2,0,0,0,0,2,1,0,3,1,1,1,1,1,0,1,1,5,1,0,0,1,2,0,1,1,5,1,2,0,0,2,1,0,1,1,0,0,1,0,0,0,2,0,2,0,1,0,3,1,0,1,2,0,0,0,3,0,5,0,0,0,0,2,2,0,0,1,0,0,3,1,5,1,1,0,0,0,0,0,0,0,1,3,1,0,0,1" [[]]

private noncomputable def right029Row1Part3 : List ℕ := native_gaps% "1,1,0,8,3,0,0,0,0,2,0,0,1,1,2,0,0,1,1,0,2,4,2,0,0,3,1,0,1,1,2,0,1,0,2,0,2,0,2,0,0,0,5,0,0,2,0,0,2,2,1,2,3,1,0,1,1,0,0,3,2,0,5,4,1,0,3,0,4,2,2,1,1,1,0,0,0,0,2,0,3,0,1,0,0,1,1,2,0,0,3,0,1,0,0,0,1,2,0,1,1,0,3,1,2,0,1,1,1,3,0,1,0,0,2,4,0,0,0,0,0,0,1,2,2,0,0,0" [right029Row1Part4]

private noncomputable def right029Row1Part2 : List ℕ := native_gaps% "0,1,7,0,1,1,0,2,4,0,0,3,3,2,2,2,1,1,0,0,2,1,0,0,0,1,0,0,2,0,0,1,1,3,1,0,0,0,0,2,1,1,0,1,1,0,2,1,1,0,2,0,2,0,0,0,2,1,2,6,0,1,1,0,1,0,0,0,0,0,1,0,3,3,0,2,2,0,4,0,0,0,0,0,1,0,1,0,1,1,0,0,0,3,0,4,0,0,2,2,0,3,1,0,0,0,0,0,2,1,1,3,1,2,2,0,0,0,0,0,2,1,0,1,0,1,0,1" [right029Row1Part3]

private noncomputable def right029Row1Part1 : List ℕ := native_gaps% "2,0,0,0,1,0,0,1,1,0,3,6,1,0,0,0,0,1,0,0,0,0,4,2,0,1,5,0,2,0,0,2,3,2,5,0,0,4,2,0,2,3,0,0,1,3,0,1,1,1,0,0,0,0,0,0,0,2,0,0,0,0,1,3,1,0,0,1,0,0,0,1,2,0,0,0,2,0,2,0,2,2,3,2,0,0,0,2,1,2,0,1,3,1,2,1,0,0,0,0,2,1,0,3,2,1,0,0,1,2,0,8,2,0,0,1,0,5,0,0,0,1,0,0,0,0,0,4" [right029Row1Part2]

private noncomputable def right029Row1Part0 : List ℕ := native_gaps% "1,1,1,1,5,0,1,0,1,1,0,4,0,0,2,0,3,0,0,0,1,2,0,0,0,0,0,0,1,0,4,0,2,2,0,1,0,1,0,0,0,0,0,1,1,0,2,0,0,0,0,0,0,0,1,1,0,2,0,2,1,0,2,0,1,5,0,0,0,1,1,0,0,0,1,1,4,2,1,0,0,0,1,0,7,4,1,0,1,2,1,0,0,0,0,1,3,0,2,2,0,0,3,0,0,0,1,0,1,2,0,0,2,2,1,3,2,1,0,0,0,2,1,0,4,4,1,4" [right029Row1Part1]

private noncomputable def right029Row1 : List ℕ := right029Row1Part0

private noncomputable def right029Row2Part4 : List ℕ := native_gaps% "5,0,0,3,1,7,0,0,1,1,1,0,1,0,0,0,3,3,0,0,6,0,0,1,1,0,1,1,3,2,0,4,0,2,0,0,1,0,0,0,0,0,4,2,3,0,1,0,0,1,1,6,1,0,1,1,0,2,2,0,0,1,1,0,2,0,0,0,1,1,0,0,0,2,0,0,2,0,1,1,1,0,4,0,1,1,0" [[]]

private noncomputable def right029Row2Part3 : List ℕ := native_gaps% "1,2,2,1,0,0,0,1,2,1,3,3,0,0,0,0,0,0,10,0,2,0,0,2,1,0,4,2,0,0,3,1,0,0,2,2,5,0,0,0,0,2,0,6,0,0,1,0,0,0,0,1,0,0,0,2,0,0,0,2,0,0,2,1,0,2,0,0,1,0,2,0,3,1,1,0,0,2,1,1,4,1,0,0,0,1,2,2,2,1,1,1,0,2,3,4,0,0,0,1,1,0,0,1,0,0,0,2,0,1,0,0,0,1,0,1,2,1,1,1,0,0,0,0,0,1,3,1" [right029Row2Part4]

private noncomputable def right029Row2Part2 : List ℕ := native_gaps% "4,2,3,0,0,1,0,0,4,0,4,3,2,4,2,2,0,0,0,0,2,2,2,6,1,0,2,0,1,0,0,0,0,1,2,1,2,3,9,1,0,3,0,2,0,0,1,1,1,1,1,0,0,0,0,8,0,1,0,0,0,3,2,0,1,0,1,1,0,1,0,2,2,3,0,0,1,1,1,2,4,0,0,1,0,0,0,2,0,2,5,0,0,1,3,0,1,0,0,0,1,2,2,0,1,1,0,4,0,0,1,0,5,0,1,0,1,0,2,1,0,4,3,1,0,1,0,1" [right029Row2Part3]

private noncomputable def right029Row2Part1 : List ℕ := native_gaps% "0,0,0,2,0,1,0,0,1,1,0,2,0,0,0,0,0,0,0,2,0,3,0,4,0,0,0,0,4,3,3,0,5,0,1,0,0,1,0,1,0,0,1,0,0,1,0,0,1,1,0,2,0,0,2,0,0,1,2,0,0,0,4,0,0,5,0,0,0,6,0,1,0,1,0,0,0,0,2,1,0,5,1,1,1,1,5,2,0,0,1,0,1,0,6,0,1,2,4,0,1,0,0,2,2,5,0,1,0,2,1,0,1,4,1,0,3,0,0,0,2,1,0,1,0,2,3,0" [right029Row2Part2]

private noncomputable def right029Row2Part0 : List ℕ := native_gaps% "0,2,0,4,0,0,3,1,0,0,0,3,0,0,0,0,1,0,0,0,0,4,0,2,1,1,0,0,0,0,0,0,1,1,2,1,0,0,0,0,0,3,4,2,0,0,4,0,0,0,2,1,0,1,1,1,0,0,0,1,0,0,5,0,0,1,1,0,0,3,0,3,1,1,0,2,0,1,0,0,4,1,1,1,4,2,1,1,0,0,0,6,0,1,4,0,2,1,0,4,0,0,4,1,0,3,0,0,3,2,4,0,1,6,1,0,6,2,0,0,0,1,1,1,2,0,0,7" [right029Row2Part1]

private noncomputable def right029Row2 : List ℕ := right029Row2Part0

private noncomputable def right029Row3Part4 : List ℕ := native_gaps% "2,0,0,0,3,0,2,0,0,3,1,2,0,2,1,0,2,0,1,1,1,0,2,0,0,0,0,0,1,3,0,1,0,4,0,1,2,0,1,0,1,0,0,0,1,0,2,0,0,5,3,0,0,0,0,5,0,2,1,1,3,2,4,0,0,1,0,0,1,2,0,5,0,0,0,0,0,0,0,3,1,2,1,0,2,0,0,0,2,1,1,0,0,2,2,0,0,0,1,1,1,2,2" [[]]

private noncomputable def right029Row3Part3 : List ℕ := native_gaps% "2,1,0,1,0,0,0,1,5,1,1,0,1,1,0,0,3,2,0,0,5,0,1,2,0,1,0,2,2,0,0,0,0,0,1,1,6,0,0,0,1,1,0,0,0,1,0,4,1,1,0,1,3,4,1,0,1,0,0,1,0,0,0,0,0,3,7,2,3,0,0,1,1,0,0,0,0,0,0,0,1,0,2,0,1,0,3,6,0,0,2,0,0,4,1,2,0,0,2,0,0,1,0,0,1,1,1,0,0,0,1,1,1,0,0,0,0,0,0,1,1,1,1,0,0,1,6,5" [right029Row3Part4]

private noncomputable def right029Row3Part2 : List ℕ := native_gaps% "7,0,0,0,4,1,0,0,2,0,0,0,1,1,1,0,3,2,1,1,1,0,0,1,0,0,1,1,2,0,1,0,0,8,1,0,0,1,2,0,2,1,0,1,0,1,0,0,0,5,3,0,8,2,0,0,1,0,0,0,0,0,1,2,2,0,0,0,0,3,0,0,0,2,0,2,0,0,1,0,3,0,1,0,2,2,1,0,1,2,0,0,0,0,0,1,2,0,3,0,1,1,6,0,6,0,6,0,0,5,0,0,5,1,3,3,1,0,0,2,0,4,5,1,0,5,0,8" [right029Row3Part3]

private noncomputable def right029Row3Part1 : List ℕ := native_gaps% "4,3,0,0,1,5,5,0,0,0,0,0,1,1,2,0,0,0,0,1,8,3,1,0,2,1,0,1,0,1,1,1,2,0,5,0,0,1,1,0,1,4,0,1,2,0,0,0,0,1,0,1,0,0,0,1,2,0,0,2,1,1,2,0,3,0,1,0,3,0,0,0,0,0,3,0,0,1,0,0,0,0,0,0,1,0,1,1,0,0,0,0,0,0,2,0,1,3,0,0,0,0,2,0,1,1,4,0,0,0,2,0,0,1,2,0,0,1,0,1,2,1,3,0,0,2,1,1" [right029Row3Part2]

private noncomputable def right029Row3Part0 : List ℕ := native_gaps% "0,1,6,0,1,0,0,0,0,1,0,0,5,0,0,4,0,2,0,0,4,2,0,0,0,1,3,1,2,0,0,0,0,3,1,1,2,1,4,0,1,1,3,6,0,1,1,0,3,1,0,0,0,0,0,0,0,2,0,0,0,0,1,3,0,4,0,0,0,0,0,0,1,0,0,1,0,0,1,1,1,1,2,0,1,1,0,3,0,1,1,0,0,1,0,0,0,1,1,0,8,0,0,0,0,1,0,0,0,0,4,0,0,2,2,1,0,3,0,1,7,4,0,3,0,0,0,2" [right029Row3Part1]

private noncomputable def right029Row3 : List ℕ := right029Row3Part0

private noncomputable def right029Row4Part5 : List ℕ := native_gaps% "0,3,0,1,1,0,0,8,0,0,0,3,0,0,2,0,0,4,1,0,1,1,1,0,1,1,0,1,1,0,1,0,1,0,1" [[]]

private noncomputable def right029Row4Part4 : List ℕ := native_gaps% "0,6,3,0,0,1,1,0,0,0,0,0,3,0,2,0,0,0,1,1,1,0,1,1,2,0,0,6,0,2,0,0,0,0,0,0,2,0,0,0,1,0,0,1,1,2,0,1,0,0,1,3,0,0,1,0,3,0,0,5,0,2,0,2,0,3,0,1,0,1,0,0,0,0,0,0,0,1,2,0,6,0,1,0,0,1,0,1,0,1,4,1,2,5,0,1,0,0,0,0,1,0,1,0,0,0,0,1,0,0,3,1,0,3,3,0,0,3,0,0,1,1,0,0,1,0,1,0" [right029Row4Part5]

private noncomputable def right029Row4Part3 : List ℕ := native_gaps% "0,0,0,0,0,3,0,1,2,0,3,0,1,0,0,0,1,0,0,0,1,2,0,1,1,0,1,1,0,0,0,2,0,5,0,2,0,2,1,1,0,0,0,0,0,0,0,1,0,0,1,1,0,0,4,1,1,0,0,0,2,0,2,1,1,1,1,1,0,1,2,1,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,1,0,0,0,0,2,0,0,3,2,3,6,0,8,3,1,0,2,0,0,1,0,2,0,0,1,0,2,1,0,0,2,1,1,0,1,2,2,1,0" [right029Row4Part4]

private noncomputable def right029Row4Part2 : List ℕ := native_gaps% "0,0,2,2,1,2,0,0,0,1,0,0,6,3,2,0,2,0,0,1,3,1,2,0,0,3,0,0,0,1,1,2,3,1,1,0,4,0,1,0,1,0,2,0,0,3,0,0,3,0,0,1,0,1,0,1,0,1,2,0,0,1,1,0,0,0,2,0,0,1,0,0,2,0,3,0,0,0,1,0,0,2,2,0,0,2,0,2,1,3,0,0,0,1,2,0,1,1,0,1,1,2,0,0,0,0,0,3,0,2,0,0,1,1,1,2,2,0,0,1,3,2,0,0,1,0,1,2" [right029Row4Part3]

private noncomputable def right029Row4Part1 : List ℕ := native_gaps% "0,1,0,1,0,0,0,1,2,1,0,1,0,1,0,2,1,0,0,1,2,2,0,1,0,0,0,0,3,0,0,0,0,3,2,0,0,0,0,1,1,2,1,1,1,0,3,4,8,0,0,1,1,0,4,1,1,2,1,0,2,2,1,3,0,1,2,1,0,1,0,0,1,1,1,0,1,0,0,0,0,0,3,5,0,1,0,1,1,1,1,0,2,0,2,0,2,3,1,0,0,0,2,0,1,0,0,0,1,2,2,2,1,0,1,0,0,1,0,0,0,0,0,0,0,3,1,1" [right029Row4Part2]

private noncomputable def right029Row4Part0 : List ℕ := native_gaps% "0,1,0,1,1,0,0,1,1,2,0,2,0,2,0,1,0,0,1,0,1,0,0,0,0,2,0,1,0,3,1,0,1,1,6,1,0,0,3,0,0,1,0,0,0,0,5,0,2,0,1,0,0,1,0,0,0,0,0,2,0,0,0,4,0,1,2,1,7,0,0,0,0,0,1,0,0,3,0,0,0,0,0,0,0,2,0,0,0,0,1,0,0,1,0,2,0,0,1,1,0,0,0,1,1,0,0,1,0,1,1,0,0,2,1,1,1,0,0,5,0,1,2,0,1,0,0,1" [right029Row4Part1]

private noncomputable def right029Row4 : List ℕ := right029Row4Part0

private noncomputable def right029Row5Part4 : List ℕ := native_gaps% "1,2,3,1,0,0,3,0,0,1,3,0,0,4,2,4,1,1,0,1,0,2,0,2,1,2,0,0,1,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,7,0,2,0,3,0,0,0,1,1,0,0,1,2,4,0,1,0,0,2,1,0,0,2,2,0,1,0,1,1,1,3,0,0,1,0,0,1,1,0,1,0,0,0,1,1,0,0,1,0,0,0,0,0,0" [[]]

private noncomputable def right029Row5Part3 : List ℕ := native_gaps% "0,2,2,2,0,0,0,0,0,0,0,0,10,0,2,0,1,1,0,1,1,1,3,1,9,2,0,1,2,1,0,0,2,0,7,1,0,3,9,0,0,2,0,1,1,0,3,0,3,0,0,0,1,3,4,0,0,0,0,0,1,0,0,1,0,3,1,0,0,0,0,0,1,2,0,1,1,0,5,0,2,1,0,0,1,0,0,0,1,1,2,0,1,1,0,0,0,0,0,3,3,0,0,2,2,1,0,0,1,1,2,2,0,0,1,0,1,0,0,0,0,0,1,0,0,2,1,6" [right029Row5Part4]

private noncomputable def right029Row5Part2 : List ℕ := native_gaps% "1,0,0,0,0,1,1,2,0,0,1,4,0,2,7,0,0,2,2,0,2,2,0,1,0,0,0,2,1,0,1,0,0,4,1,0,1,1,2,1,1,0,0,1,2,6,0,0,0,2,1,1,2,0,0,0,2,0,1,0,1,0,1,1,2,1,0,3,0,1,3,2,0,0,1,1,0,1,1,0,0,0,8,1,2,0,2,0,1,2,11,0,2,4,0,2,3,2,7,0,0,2,1,0,1,1,1,1,1,1,0,2,3,2,3,0,0,1,0,0,0,1,1,1,3,1,4,1" [right029Row5Part3]

private noncomputable def right029Row5Part1 : List ℕ := native_gaps% "0,3,0,4,1,0,2,2,0,1,0,1,0,2,1,2,1,1,5,0,4,5,0,1,1,1,1,0,1,0,3,0,3,1,1,3,0,0,0,1,0,0,2,1,2,3,4,0,1,0,0,1,0,0,0,2,0,2,1,0,0,0,1,2,0,0,1,0,4,0,0,0,0,0,0,1,4,1,1,0,0,2,0,1,0,0,0,0,0,0,0,6,4,3,1,0,0,1,1,1,2,0,1,0,0,0,1,2,2,2,0,1,0,0,0,1,1,0,1,0,2,0,4,3,0,0,1,0" [right029Row5Part2]

private noncomputable def right029Row5Part0 : List ℕ := native_gaps% "0,2,4,0,1,0,0,2,0,1,0,2,0,1,0,2,1,1,0,0,0,1,7,0,2,2,1,0,1,2,0,0,0,0,1,1,2,3,0,0,0,0,0,1,0,0,0,1,0,0,0,1,4,2,0,0,4,1,0,1,1,3,0,0,0,0,1,4,4,1,0,1,2,0,2,1,0,2,1,2,1,0,0,4,4,1,1,1,1,5,1,0,0,0,1,0,0,0,0,0,0,0,1,0,1,1,0,0,1,0,2,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,0" [right029Row5Part1]

private noncomputable def right029Row5 : List ℕ := right029Row5Part0

private noncomputable def right029Row6Part4 : List ℕ := native_gaps% "4,4,3,0,1,0,0,1,1,2,4,1,9,0,1,0,0,0,0,2,1,2,4,0,1,0,2,0,1,1,0,0,1,0,2,1,1,4,4,0,6,0,0,1,1,0,1,0,1,0,3,1,0,0,0,1,3,0,4,0,1,0,0,0,2,1,0,1,1,0,0,1,1,1,0,0,1,3,2,1,0,0,0,0,0,0,2,0,2,0,0,1,2,2,3,0,4,0,0,0,2,0,0,1,1,2,1,0,0,0,2,0,1,2,0" [[]]

private noncomputable def right029Row6Part3 : List ℕ := native_gaps% "2,0,1,1,6,1,2,0,0,0,0,0,2,1,0,0,2,1,0,0,0,2,0,0,0,0,1,0,0,0,0,2,2,3,0,1,3,2,0,0,2,1,1,0,2,0,1,3,0,0,2,0,0,0,0,0,0,2,1,0,0,0,0,6,1,2,5,2,1,1,0,0,0,1,0,0,4,0,6,2,0,0,4,0,0,0,3,0,1,1,6,0,5,0,1,0,3,0,0,0,2,0,1,0,0,0,0,1,1,0,1,1,1,1,0,2,1,1,0,0,0,3,2,0,1,0,0,0" [right029Row6Part4]

private noncomputable def right029Row6Part2 : List ℕ := native_gaps% "1,0,0,0,3,0,3,0,1,1,3,0,3,1,0,0,1,0,1,1,2,0,0,0,0,2,4,0,2,0,0,0,1,0,1,2,0,0,1,0,0,0,0,0,4,0,7,1,1,2,1,1,1,0,1,3,2,2,0,1,3,0,5,1,9,0,1,2,4,1,2,0,0,1,1,5,1,0,0,0,2,1,0,0,0,0,3,1,0,5,0,4,0,0,0,1,0,0,1,3,1,0,1,0,0,0,0,1,0,1,0,0,1,1,0,0,0,0,3,0,1,0,2,0,0,1,0,0" [right029Row6Part3]

private noncomputable def right029Row6Part1 : List ℕ := native_gaps% "0,0,1,0,0,4,0,0,0,1,2,0,1,2,0,0,2,0,0,0,1,0,2,1,1,2,0,1,2,1,0,4,1,5,0,0,0,1,11,1,1,1,0,0,1,0,2,1,1,1,2,1,4,0,0,0,0,0,1,0,1,1,0,1,0,2,1,0,1,0,2,0,1,1,0,0,1,0,1,2,0,1,0,0,0,0,2,0,0,0,2,3,1,0,1,0,1,0,5,0,0,0,1,0,0,4,1,0,0,1,0,2,0,1,0,1,0,1,0,0,0,1,2,2,0,0,0,0" [right029Row6Part2]

private noncomputable def right029Row6Part0 : List ℕ := native_gaps% "0,0,0,0,3,0,1,0,1,0,6,2,0,0,0,1,1,0,1,0,0,0,0,3,0,0,1,1,0,0,0,0,6,0,0,1,2,0,0,1,0,0,2,2,2,1,0,1,0,0,6,0,0,1,0,1,0,2,0,0,0,1,2,0,0,0,1,0,1,0,2,1,1,2,0,0,0,0,7,0,1,0,4,3,0,0,0,1,2,0,1,0,2,0,2,0,4,2,1,0,0,1,5,2,1,1,1,1,0,0,0,2,1,0,0,1,0,1,0,1,6,3,0,1,5,0,1,0" [right029Row6Part1]

private noncomputable def right029Row6 : List ℕ := right029Row6Part0

private noncomputable def right029Row7Part4 : List ℕ := native_gaps% "0,0,0,0,0,0,2,5,0,0,3,0,0,0,1,0,0,0,1,0,1,1,0,1,2,0,0,0,1,2,2,0,3,9,0,0,7,2,4,3,1,0,2,0,2,4,1,1,0,1,0,0,0,0,1,0,0,0,0,0,3,1,0,1,0,1,1,1,2,0,0,0,0,4,1,3,1,0,0,0,0,0,0,0,5" [[]]

private noncomputable def right029Row7Part3 : List ℕ := native_gaps% "1,0,2,1,0,2,1,2,1,4,4,0,0,0,0,0,0,0,0,0,3,2,1,0,1,1,0,0,3,0,0,0,0,1,0,1,1,0,0,0,0,2,0,0,0,1,0,1,2,1,0,1,0,1,1,1,1,0,1,0,1,3,0,0,2,1,0,0,1,0,5,4,0,0,0,1,1,0,1,0,1,1,2,2,2,0,0,0,1,0,0,1,0,1,0,0,1,0,0,1,2,0,1,0,0,0,0,2,1,0,0,1,0,1,0,0,1,1,0,2,1,5,0,0,0,1,1,0" [right029Row7Part4]

private noncomputable def right029Row7Part2 : List ℕ := native_gaps% "0,3,4,0,0,1,0,2,0,1,2,0,2,0,8,0,1,0,0,0,1,0,0,1,0,0,1,1,1,0,0,0,1,1,3,0,0,4,2,6,2,1,0,0,0,2,0,0,2,0,2,4,0,2,1,0,0,1,2,0,0,0,0,7,1,1,4,1,2,0,1,0,1,2,0,2,4,1,0,0,2,1,3,1,1,0,0,0,1,2,0,0,1,1,2,0,1,0,2,0,1,2,0,7,0,1,0,6,1,0,2,0,0,0,0,1,0,1,0,1,7,8,1,7,1,1,5,1" [right029Row7Part3]

private noncomputable def right029Row7Part1 : List ℕ := native_gaps% "0,0,1,1,0,2,2,3,2,0,1,0,1,1,3,6,0,3,0,1,2,0,0,5,2,1,3,0,1,0,0,0,0,0,0,1,0,0,0,0,2,0,0,0,1,0,2,1,2,2,1,0,4,2,3,1,1,2,0,0,0,2,0,2,1,2,0,0,0,2,2,1,0,0,1,0,0,6,1,0,1,2,1,0,1,1,1,1,0,1,0,0,1,0,1,0,0,1,2,1,0,3,4,1,1,2,1,0,0,0,3,0,2,4,0,2,0,2,1,2,0,0,2,0,3,1,5,0" [right029Row7Part2]

private noncomputable def right029Row7Part0 : List ℕ := native_gaps% "0,0,0,1,0,0,1,2,1,1,0,3,0,1,1,0,0,0,0,3,0,0,0,2,2,2,2,1,0,0,1,2,0,1,3,0,2,0,2,4,2,0,4,3,4,0,5,0,0,2,1,0,0,0,3,2,0,0,4,2,1,2,2,2,0,3,2,8,2,0,1,1,2,0,0,1,4,1,3,0,0,2,1,0,3,0,1,0,3,0,0,1,1,1,3,0,1,0,0,1,0,2,0,1,0,0,2,1,0,3,0,1,0,1,1,3,0,3,5,0,2,3,0,0,1,2,1,1" [right029Row7Part1]

private noncomputable def right029Row7 : List ℕ := right029Row7Part0

private noncomputable def rightGaps029 : List (List ℕ) := [right029Row0, right029Row1, right029Row2, right029Row3, right029Row4, right029Row5, right029Row6, right029Row7]

private theorem leftMask029 :
    (leftGaps029.map gapMask == (sourceTransposeA.drop 232).take 8) = true := by
  decide +kernel

private theorem rightMask029 :
    (rightGaps029.map gapMask == (quotientTransposeRows.drop 232).take 8) = true := by
  decide +kernel

private theorem products029 :
    (leftGaps029.map (gapRow quotientTransposeRows) == rightGaps029.map (gapRow targetA)) = true := by
  decide +kernel

theorem block029 :
    checkEqualProducts quotientTransposeRows targetA
      ((sourceTransposeA.drop 232).take 8) ((quotientTransposeRows.drop 232).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask029) (beq_iff_eq.mp rightMask029)
    (beq_iff_eq.mp products029)

private noncomputable def left030Row0Part5 : List ℕ := native_gaps% "5,0,5,0,1,1,1,2,0,0,2,0,1,0,0,0,1,4,0,0,0,2,4,0,1,3,0,0,0,1,0,3,4,0,0,0,0" [[]]

private noncomputable def left030Row0Part4 : List ℕ := native_gaps% "3,1,1,0,1,2,0,4,3,0,1,0,3,1,1,0,4,0,0,1,5,0,1,2,1,2,1,0,0,0,3,0,1,1,6,0,1,0,1,0,0,3,0,0,0,0,1,0,1,1,0,1,0,0,3,0,3,1,3,1,0,2,3,0,0,0,2,1,0,0,1,1,0,1,2,2,1,0,0,2,4,2,5,0,3,1,2,0,2,2,0,0,0,1,0,1,0,1,3,1,1,0,3,1,1,0,0,0,1,1,1,3,3,1,4,0,3,0,4,0,2,0,0,2,3,0,6,1" [left030Row0Part5]

private noncomputable def left030Row0Part3 : List ℕ := native_gaps% "0,0,6,4,0,1,0,3,1,0,0,7,0,0,0,3,0,0,1,0,0,1,1,0,1,0,0,1,2,0,0,1,0,6,0,0,3,0,1,0,3,0,0,3,3,1,1,0,0,0,0,3,0,1,0,0,1,0,1,0,0,1,0,4,1,5,1,0,2,2,0,5,0,3,0,0,0,0,3,0,3,2,2,0,0,1,1,0,0,0,0,1,0,0,1,2,0,0,1,0,8,1,1,1,2,0,1,4,2,2,1,0,1,3,1,0,0,1,0,0,1,0,0,1,0,1,1,1" [left030Row0Part4]

private noncomputable def left030Row0Part2 : List ℕ := native_gaps% "1,3,0,2,1,2,2,1,0,0,0,1,1,0,1,0,0,0,0,4,0,1,2,0,0,0,0,0,0,7,0,3,3,3,0,2,0,1,0,2,0,1,0,0,2,2,0,0,0,1,1,0,1,1,0,2,0,1,0,1,1,0,0,1,1,2,0,0,2,1,1,0,1,0,0,2,3,2,3,1,2,2,1,0,0,0,2,1,0,2,1,5,0,0,0,0,2,1,1,1,1,1,1,0,0,3,4,0,1,0,0,2,0,1,0,2,6,5,0,0,0,0,0,1,4,1,1,1" [left030Row0Part3]

private noncomputable def left030Row0Part1 : List ℕ := native_gaps% "1,1,0,0,2,0,1,4,0,0,2,0,2,0,0,1,2,2,0,2,0,0,0,0,0,4,0,4,2,1,1,2,0,0,0,0,0,1,0,0,0,0,0,2,0,0,2,0,0,0,1,0,0,0,1,2,3,0,1,4,2,0,0,0,5,3,3,0,2,0,2,0,3,2,0,0,2,1,0,1,1,0,1,0,0,1,0,1,1,0,0,2,0,0,0,1,0,1,0,0,0,1,0,0,0,1,3,1,3,2,2,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,1,0" [left030Row0Part2]

private noncomputable def left030Row0Part0 : List ℕ := native_gaps% "0,2,4,0,0,0,1,2,1,0,1,0,1,1,0,0,0,2,1,1,0,1,0,0,1,0,0,2,1,0,5,0,1,3,0,1,0,0,1,1,0,3,4,1,1,3,0,2,0,0,0,0,0,0,1,0,1,1,0,1,0,0,0,0,0,2,1,0,2,0,0,0,1,77,0,19,1,1,0,2,3,0,0,0,1,0,0,0,5,1,1,5,0,0,0,2,0,0,0,0,9,1,2,0,0,0,1,2,0,4,4,2,0,1,3,2,7,1,0,0,1,4,0,2,1,1,2,2" [left030Row0Part1]

private noncomputable def left030Row0 : List ℕ := left030Row0Part0

private noncomputable def left030Row1Part5 : List ℕ := native_gaps% "1,8,1,4,0,0,0,5,0,1,0,0,4,0,2,2,1,0,1,0,0,1,4,0,1,2,0,4,0,0,2,0,2,4,3,1,1,3,0,0,1,1,1,0" [[]]

private noncomputable def left030Row1Part4 : List ℕ := native_gaps% "3,1,1,2,1,1,0,1,3,1,4,3,2,0,6,0,0,0,0,4,3,0,0,1,0,1,1,4,0,0,0,0,1,0,3,0,1,0,0,1,0,1,3,2,0,1,1,4,0,0,0,3,0,1,0,0,0,0,2,0,0,0,0,0,2,1,1,0,1,0,0,0,1,2,0,0,0,0,0,5,4,0,0,0,0,3,2,3,0,3,1,0,0,2,0,0,0,1,3,0,0,1,0,1,1,0,0,3,1,3,0,0,1,2,0,0,1,1,0,0,0,6,1,0,2,1,2,2" [left030Row1Part5]

private noncomputable def left030Row1Part3 : List ℕ := native_gaps% "0,0,1,1,4,0,0,0,3,3,5,0,1,0,0,0,0,0,0,0,0,3,0,0,1,2,3,0,0,1,0,0,0,0,0,0,0,1,3,0,1,1,3,2,2,0,0,0,2,0,4,1,0,0,0,0,2,0,0,2,3,1,1,0,1,1,1,0,1,2,2,0,2,3,2,3,0,1,2,1,1,0,5,1,2,0,0,0,0,3,0,0,1,0,2,1,0,3,2,0,2,0,0,0,3,3,0,0,1,2,2,0,1,1,0,1,1,0,0,1,0,1,1,0,1,2,0,0" [left030Row1Part4]

private noncomputable def left030Row1Part2 : List ℕ := native_gaps% "0,0,0,0,1,3,0,0,4,0,2,0,0,3,0,2,2,0,1,2,3,2,0,5,1,1,2,0,2,0,0,0,0,0,2,0,1,0,4,3,1,2,1,1,1,0,1,4,1,2,2,1,0,2,1,1,2,1,1,1,1,0,1,0,0,0,0,2,0,0,0,1,0,0,0,0,2,0,0,0,0,0,0,0,0,1,0,0,0,3,4,0,0,2,1,0,0,3,2,0,1,2,1,0,1,5,8,2,0,0,2,0,1,0,1,3,0,2,7,2,0,5,0,2,4,0,1,0" [left030Row1Part3]

private noncomputable def left030Row1Part1 : List ℕ := native_gaps% "0,0,3,0,0,0,0,0,0,1,0,1,0,0,6,1,1,1,1,2,0,0,1,2,0,0,1,2,1,0,2,3,1,1,0,0,2,1,1,1,4,0,2,0,0,3,0,1,1,1,0,2,0,2,0,0,1,5,0,3,3,1,1,0,0,3,2,0,0,0,1,0,1,0,2,1,0,3,0,0,1,2,0,0,0,0,1,0,2,1,0,7,0,2,3,0,1,2,1,0,0,1,0,0,0,0,0,2,0,0,3,2,0,1,5,0,1,0,0,0,0,4,0,0,1,0,0,1" [left030Row1Part2]

private noncomputable def left030Row1Part0 : List ℕ := native_gaps% "1,2,0,6,0,0,1,0,0,0,1,1,1,0,1,0,1,1,0,1,1,0,0,1,0,1,0,0,0,0,1,0,0,1,0,1,0,0,0,2,0,4,0,0,0,4,0,0,0,0,1,7,0,3,1,1,0,0,0,0,0,1,1,0,1,2,0,0,3,0,1,0,1,78,23,0,0,5,0,2,1,0,0,1,0,1,1,1,0,3,2,0,0,1,4,0,0,1,3,0,1,0,1,3,0,0,4,1,2,5,0,0,3,0,1,0,0,1,1,0,0,1,0,0,0,0,0,0" [left030Row1Part1]

private noncomputable def left030Row1 : List ℕ := left030Row1Part0

private noncomputable def left030Row2Part5 : List ℕ := native_gaps% "0,0,0,0,0,0,0,0,2,1,2,0,1,0,0,0,0,1,0,1,3,2,1,1,1,0,1,3,1,0,1,0,1,5,0" [[]]

private noncomputable def left030Row2Part4 : List ℕ := native_gaps% "0,0,0,0,0,1,2,3,2,0,0,0,0,0,3,1,3,0,1,0,0,0,0,0,0,1,4,1,1,2,2,5,1,1,1,3,0,2,1,0,0,4,3,1,1,3,1,2,4,4,4,0,3,2,0,1,0,0,1,4,0,2,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,3,1,0,1,2,3,0,0,4,2,3,0,0,0,0,0,2,1,0,2,0,1,0,1,0,1,5,0,0,1,1,0,0,0,1,0,4,1,1,3,0,1,15,1,0,1,1,0,1,0,2" [left030Row2Part5]

private noncomputable def left030Row2Part3 : List ℕ := native_gaps% "0,0,2,1,0,0,0,1,0,0,0,0,0,0,2,3,0,1,0,1,0,2,1,0,0,0,1,0,0,0,2,0,0,0,4,0,0,1,0,0,0,3,1,0,3,1,0,0,0,2,0,1,1,0,1,2,0,2,0,2,1,0,3,3,1,1,1,1,2,0,0,2,1,0,1,1,1,0,3,1,1,0,2,0,1,0,0,0,4,1,0,0,0,0,3,2,1,2,0,2,1,0,3,0,1,0,0,2,0,1,1,2,0,1,0,1,0,1,0,0,0,2,0,1,0,1,3,2" [left030Row2Part4]

private noncomputable def left030Row2Part2 : List ℕ := native_gaps% "0,0,1,3,4,3,0,1,0,6,1,0,2,1,5,3,0,0,2,0,0,0,0,0,1,0,1,7,1,1,1,0,0,0,2,0,0,1,6,1,1,0,2,2,0,4,1,2,0,0,1,2,0,0,1,0,0,4,1,0,5,1,0,3,0,6,0,0,0,1,6,4,1,0,1,1,0,3,1,1,1,2,0,0,0,3,0,1,0,0,0,0,2,0,3,0,0,1,1,2,0,0,2,3,0,0,0,0,1,0,1,0,2,1,0,1,3,0,1,2,0,0,0,0,2,1,1,1" [left030Row2Part3]

private noncomputable def left030Row2Part1 : List ℕ := native_gaps% "0,1,0,5,0,0,0,0,1,0,2,2,0,0,0,1,1,0,0,0,1,1,1,2,2,2,1,1,0,4,1,5,4,1,1,0,0,0,0,0,0,0,2,2,2,1,2,0,1,1,1,3,3,2,0,3,5,5,0,0,1,0,0,0,1,3,0,0,0,0,6,0,0,0,0,1,1,0,0,0,1,4,2,0,4,2,1,0,0,0,1,0,0,3,0,1,1,7,0,1,1,0,1,0,4,3,0,0,0,0,0,1,0,0,4,0,0,0,2,0,0,2,0,0,0,3,0,1" [left030Row2Part2]

private noncomputable def left030Row2Part0 : List ℕ := native_gaps% "0,0,1,1,3,1,1,0,0,1,0,0,1,1,1,0,1,1,1,1,0,0,0,6,2,0,0,0,3,0,0,0,0,4,1,1,0,0,0,2,0,0,2,0,0,0,1,1,5,1,0,1,0,1,0,0,0,1,0,0,0,0,2,10,1,85,20,4,0,2,1,1,0,1,0,2,1,0,1,0,2,3,1,1,0,0,1,0,0,1,0,6,5,1,1,3,5,3,0,2,0,0,2,1,1,0,0,2,0,0,3,3,0,0,1,0,0,0,0,0,1,1,0,0,2,0,1,1" [left030Row2Part1]

private noncomputable def left030Row2 : List ℕ := left030Row2Part0

private noncomputable def left030Row3Part5 : List ℕ := native_gaps% "1,2,0,0,3,0,0,0,0,1,0,0,0,1,0,2,0,2,0,0,0,0,3,0,0,1,2,1,0,0,0,1,0,1,0,2,0,0,0,0,0,0,1,1,1,2,2,1,1,0,0" [[]]

private noncomputable def left030Row3Part4 : List ℕ := native_gaps% "0,1,1,0,1,4,5,0,3,5,1,0,0,2,0,4,4,0,1,0,0,0,2,3,1,0,0,0,1,1,2,0,0,0,2,1,1,0,0,0,4,0,3,0,1,1,1,1,1,1,0,3,0,0,3,0,2,0,1,0,1,2,1,0,0,2,0,0,0,1,1,5,0,0,1,0,0,1,3,0,0,1,2,1,0,0,0,0,0,1,0,0,0,1,0,0,0,3,0,0,3,7,1,2,1,0,1,4,1,0,4,0,1,1,1,2,4,4,0,1,0,0,0,0,1,3,0,0" [left030Row3Part5]

private noncomputable def left030Row3Part3 : List ℕ := native_gaps% "0,1,0,0,0,2,0,0,0,4,5,3,1,1,0,0,1,1,2,0,1,1,0,1,0,0,1,0,0,0,0,1,0,2,1,0,2,0,0,3,1,0,0,0,0,0,2,2,4,1,0,0,2,1,2,0,0,0,1,2,3,1,0,0,1,1,2,0,0,0,0,0,2,0,0,0,1,0,1,4,1,0,0,1,1,3,0,0,3,0,0,1,0,1,4,1,0,1,0,0,1,1,1,0,0,2,0,2,0,5,0,0,0,0,3,1,0,2,5,0,0,0,1,7,0,0,0,0" [left030Row3Part4]

private noncomputable def left030Row3Part2 : List ℕ := native_gaps% "1,0,2,0,0,1,4,0,1,0,1,0,1,9,0,1,0,0,4,0,0,0,1,2,0,4,3,0,0,0,0,1,0,2,5,4,0,1,1,0,0,0,1,1,2,2,1,0,1,0,2,1,2,3,1,1,1,2,0,0,2,0,2,0,1,0,0,0,0,0,12,3,1,1,2,6,0,2,0,0,2,1,3,0,1,0,0,0,0,0,1,0,0,1,3,0,0,0,1,0,2,4,2,4,2,2,1,1,0,1,0,0,1,9,2,0,1,1,0,1,0,4,0,4,0,4,1,0" [left030Row3Part3]

private noncomputable def left030Row3Part1 : List ℕ := native_gaps% "5,3,0,1,2,0,0,1,0,0,3,1,1,0,1,0,3,3,0,2,0,0,0,0,0,0,1,1,2,3,1,1,0,0,0,0,4,1,3,1,0,2,4,0,1,4,2,0,3,0,0,1,0,0,0,0,0,1,0,3,4,0,2,2,0,3,0,1,0,0,0,2,0,2,3,0,1,0,1,1,0,0,2,0,0,0,1,0,2,1,2,3,0,0,4,0,0,0,1,0,0,0,0,0,0,0,2,1,0,0,2,0,0,0,4,0,1,3,1,0,1,0,1,2,1,0,1,1" [left030Row3Part2]

private noncomputable def left030Row3Part0 : List ℕ := native_gaps% "0,0,0,0,0,0,0,1,5,0,1,0,1,1,1,0,0,0,1,0,0,0,0,0,0,1,1,1,0,1,7,2,0,0,0,2,4,2,1,1,0,0,1,1,0,0,2,0,6,2,1,2,0,2,1,0,0,2,0,0,1,1,0,1,0,1,1,0,1,0,0,76,1,19,1,0,1,1,1,0,2,1,0,0,0,5,1,1,1,2,0,1,1,0,1,0,2,2,3,0,1,6,2,4,0,0,6,0,0,2,0,0,1,0,0,2,0,0,0,0,1,0,2,0,0,0,2,0" [left030Row3Part1]

private noncomputable def left030Row3 : List ℕ := left030Row3Part0

private noncomputable def left030Row4Part5 : List ℕ := native_gaps% "0,2,1,1,7,3,1,0,1,2,1,0,1,5,0,3,0,0,0,0,1,1,0,0,0,0" [[]]

private noncomputable def left030Row4Part4 : List ℕ := native_gaps% "0,0,1,0,6,2,3,1,2,2,3,1,1,0,1,0,3,5,1,0,0,1,0,0,4,5,0,0,4,1,1,0,0,1,0,4,0,0,2,4,1,1,0,0,2,1,0,0,2,0,0,0,6,0,1,3,0,1,0,1,0,3,0,1,2,1,0,2,2,1,0,0,1,0,1,0,1,2,2,0,5,0,0,3,0,0,2,3,5,0,2,1,0,1,0,0,0,2,0,0,3,1,1,4,0,0,0,1,2,5,0,0,1,1,2,0,0,3,0,1,0,1,1,1,2,1,1,0" [left030Row4Part5]

private noncomputable def left030Row4Part3 : List ℕ := native_gaps% "1,1,0,5,3,0,0,1,0,5,3,0,0,4,0,2,3,2,1,3,0,2,0,1,1,0,0,0,0,0,2,2,1,0,2,0,0,1,0,1,1,0,0,1,4,2,0,2,2,3,1,1,0,0,1,0,1,0,1,1,0,0,3,1,0,1,0,0,3,1,1,3,0,4,1,0,1,1,0,0,0,0,0,0,0,9,1,0,6,0,1,1,0,0,0,1,3,1,0,3,0,0,0,3,0,1,0,3,0,1,0,0,4,4,0,0,2,0,1,1,1,3,1,0,0,0,1,0" [left030Row4Part4]

private noncomputable def left030Row4Part2 : List ℕ := native_gaps% "1,1,0,0,0,0,1,0,0,0,1,0,0,3,0,0,0,1,1,1,1,0,2,3,0,2,0,1,0,0,0,0,3,0,0,0,1,0,0,0,0,0,2,0,2,0,0,0,2,0,1,0,0,2,0,4,3,2,1,2,1,1,8,0,3,1,0,0,1,6,1,0,1,1,1,0,1,0,0,1,0,0,0,0,3,0,0,1,1,0,0,0,2,3,2,0,4,1,0,0,1,5,0,2,2,0,2,0,1,0,0,0,0,2,0,1,0,1,5,0,2,0,0,0,1,0,0,0" [left030Row4Part3]

private noncomputable def left030Row4Part1 : List ℕ := native_gaps% "0,3,1,2,1,3,2,0,4,1,1,0,0,1,0,0,4,0,0,0,0,1,0,1,0,1,0,0,1,3,0,1,2,2,0,1,3,2,2,0,0,0,0,0,0,0,1,0,2,0,1,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,1,2,0,1,0,2,4,0,0,1,0,2,1,0,6,2,1,0,0,2,3,0,0,0,0,0,4,0,1,1,1,0,1,1,1,1,0,3,4,1,0,0,0,1,1,0,3,2,1,2,0,1,3,5,0,0,3,1,2,0,1" [left030Row4Part2]

private noncomputable def left030Row4Part0 : List ℕ := native_gaps% "3,2,0,0,2,0,1,3,1,0,0,0,1,1,4,7,0,2,4,0,1,0,0,2,0,0,3,0,0,1,0,0,1,4,0,0,0,6,0,0,0,0,0,0,0,0,0,1,0,2,2,0,4,0,1,0,0,0,0,2,1,1,3,0,78,20,0,3,0,2,0,3,3,4,4,1,2,0,0,1,1,12,0,2,1,2,0,0,2,2,4,0,3,0,1,0,3,0,2,0,0,0,3,2,1,0,2,1,0,1,0,1,2,0,0,1,0,0,0,1,2,0,1,2,4,2,0,1" [left030Row4Part1]

private noncomputable def left030Row4 : List ℕ := left030Row4Part0

private noncomputable def left030Row5Part5 : List ℕ := native_gaps% "2,1,0,0,0,0,0,2,3,1,1,2,6,0,0,1,0,1,0,1,0,1,1,0,0,3,0,2,0,0,1,0,1,0,1,1,1,3,2,0,0,0,0,0,5,0,2,0,2,1,2,0,0,0,3,3,2,0,0,0,2,1,2,1" [[]]

private noncomputable def left030Row5Part4 : List ℕ := native_gaps% "6,1,2,1,1,0,1,0,0,0,1,0,2,0,0,0,0,0,4,0,0,0,4,1,0,2,0,0,0,0,0,0,0,0,2,0,0,3,0,1,0,0,0,1,1,2,2,1,0,0,0,1,1,1,1,0,1,0,1,1,0,1,0,2,0,0,2,0,0,1,0,3,3,2,0,3,0,0,0,1,0,2,2,2,2,1,1,1,0,5,2,1,1,1,0,1,1,0,2,2,1,1,3,5,0,0,1,1,1,0,0,0,0,3,0,0,2,0,1,0,0,0,4,2,2,0,0,0" [left030Row5Part5]

private noncomputable def left030Row5Part3 : List ℕ := native_gaps% "0,1,1,0,2,0,2,0,0,2,1,1,5,1,0,0,0,0,1,0,1,0,0,1,0,2,0,0,0,0,0,0,4,0,0,0,1,0,0,0,0,1,0,1,0,0,1,1,0,2,0,3,0,0,3,1,1,0,0,0,0,0,0,0,2,0,0,0,0,4,3,0,0,4,0,0,0,0,0,1,2,2,0,0,0,0,0,0,1,0,3,0,0,0,0,1,1,0,0,0,0,2,1,3,0,3,0,0,0,1,2,1,0,2,0,0,2,0,0,6,5,1,1,0,0,0,0,1" [left030Row5Part4]

private noncomputable def left030Row5Part2 : List ℕ := native_gaps% "2,0,2,2,2,0,1,4,0,0,1,0,2,5,1,0,0,0,1,0,0,0,0,2,2,0,1,0,0,0,0,0,0,0,4,2,0,3,1,1,0,0,0,2,0,4,2,0,1,0,2,0,0,0,0,3,0,1,0,0,0,1,1,2,2,0,1,0,8,1,1,1,0,0,1,0,0,2,1,0,2,0,0,1,5,1,1,2,0,1,1,1,4,0,0,0,1,0,0,1,0,0,5,1,0,0,1,2,0,2,2,0,1,0,1,0,6,0,0,0,4,3,0,6,1,4,1,0" [left030Row5Part3]

private noncomputable def left030Row5Part1 : List ℕ := native_gaps% "0,0,0,0,4,0,0,0,1,0,1,1,0,0,0,1,0,1,0,3,1,1,1,1,2,2,0,0,0,3,3,1,0,0,0,0,1,1,2,0,2,0,5,4,1,0,0,0,1,2,1,0,3,0,2,0,1,0,1,0,0,0,0,1,2,0,0,0,0,0,0,4,0,4,2,0,6,0,1,4,0,0,0,0,1,0,2,1,0,1,0,3,0,2,0,1,1,1,2,2,0,0,1,1,0,1,0,2,5,4,0,0,0,0,3,0,5,1,0,0,1,0,1,0,1,0,2,1" [left030Row5Part2]

private noncomputable def left030Row5Part0 : List ℕ := native_gaps% "1,1,0,1,0,2,0,0,1,1,2,2,2,0,0,1,1,0,2,1,0,0,1,1,1,0,5,2,0,0,1,1,0,0,0,1,0,0,1,0,1,2,0,0,1,5,0,0,2,0,0,1,0,0,0,0,0,1,0,0,4,0,2,1,5,0,2,82,0,0,18,0,0,0,0,0,0,1,1,0,1,1,0,2,0,1,2,2,0,9,5,2,3,2,0,1,4,2,3,0,2,4,1,1,0,0,0,0,0,0,0,0,3,0,0,0,0,2,2,1,0,4,2,5,0,3,0,1" [left030Row5Part1]

private noncomputable def left030Row5 : List ℕ := left030Row5Part0

private noncomputable def left030Row6Part5 : List ℕ := native_gaps% "0,1,0,4,0,0,0,1,0,0,0,2,0,0,1,0,0,0,7,1,0,0,0,0,0,3,0,1,0,2,0,1,0,0,0,5" [[]]

private noncomputable def left030Row6Part4 : List ℕ := native_gaps% "0,0,2,3,1,1,2,2,1,1,1,2,0,0,0,0,0,1,2,1,0,0,1,1,0,2,3,0,1,1,0,0,2,1,0,0,0,0,1,0,0,1,4,0,2,0,0,0,0,1,1,0,0,1,0,0,2,0,1,0,1,1,1,0,0,0,3,0,1,0,0,0,2,1,0,1,1,0,2,0,0,1,0,0,2,1,2,0,1,0,0,3,0,3,0,2,0,0,0,0,1,0,0,0,0,1,0,0,0,0,2,1,0,0,1,1,0,1,0,0,3,0,2,4,1,1,0,2" [left030Row6Part5]

private noncomputable def left030Row6Part3 : List ℕ := native_gaps% "3,1,1,0,0,1,1,0,4,1,0,4,0,1,0,0,0,0,2,0,0,1,0,0,0,0,1,3,0,0,3,1,0,2,0,0,1,1,2,0,0,0,1,1,3,1,0,2,0,0,1,0,1,3,0,0,0,2,1,0,0,0,0,4,0,5,0,4,5,2,0,2,0,2,0,2,0,0,1,0,0,1,6,0,1,2,0,0,3,1,0,0,0,4,0,1,5,1,3,0,0,3,3,3,4,4,1,0,3,1,0,0,2,0,0,1,3,0,0,1,2,1,0,1,1,2,0,0" [left030Row6Part4]

private noncomputable def left030Row6Part2 : List ℕ := native_gaps% "6,3,2,0,2,0,0,0,0,0,0,1,5,0,2,1,0,2,0,3,0,0,0,2,1,6,1,1,1,1,3,0,1,0,6,0,0,0,1,1,1,1,2,0,0,0,3,0,2,0,0,3,1,0,0,1,0,13,0,0,1,1,5,0,1,0,2,1,0,1,1,0,0,0,0,1,0,0,2,0,0,1,0,0,0,0,0,0,0,1,2,1,1,0,0,3,0,0,2,4,1,3,0,0,1,7,2,0,1,3,0,5,1,0,0,2,0,0,1,0,7,3,1,1,3,1,1,0" [left030Row6Part3]

private noncomputable def left030Row6Part1 : List ℕ := native_gaps% "1,1,1,1,0,0,0,0,0,0,1,0,0,3,0,1,1,2,2,1,1,3,3,0,3,1,0,0,0,0,1,0,1,2,2,0,0,1,4,0,0,1,0,0,0,0,1,0,0,1,0,2,4,3,0,0,0,1,0,5,4,2,4,0,0,1,0,0,0,1,1,0,2,1,0,0,0,1,0,2,0,2,0,2,0,0,0,0,1,3,0,2,6,2,1,4,0,1,1,2,1,0,2,4,2,0,1,2,0,0,0,1,0,1,4,3,1,1,4,0,0,1,3,2,1,0,2,1" [left030Row6Part2]

private noncomputable def left030Row6Part0 : List ℕ := native_gaps% "0,3,1,7,1,0,0,0,2,0,3,1,1,1,0,2,0,0,0,0,0,1,1,0,0,0,1,0,0,0,0,3,2,0,1,2,7,0,0,1,4,0,0,0,1,2,4,1,0,0,1,1,0,1,0,3,1,0,4,2,1,2,77,0,0,19,1,0,4,1,1,0,0,1,1,2,0,3,0,2,3,0,1,2,2,0,2,6,5,0,0,1,0,3,0,2,0,3,2,1,0,0,0,4,1,3,2,0,2,3,0,0,2,0,1,1,0,0,1,1,0,2,0,0,0,1,2,0" [left030Row6Part1]

private noncomputable def left030Row6 : List ℕ := left030Row6Part0

private noncomputable def left030Row7Part5 : List ℕ := native_gaps% "0,1,1,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0,1,1,0,1,1,1,1,0,1,0,3,0,2,4,3,0,0,1,1,0,0,3,1,3,0,0,1,0,1,0,2,0,0,0,2,0,0,0,3,1,0,0,0,0,0,8,0,0,2,0" [[]]

private noncomputable def left030Row7Part4 : List ℕ := native_gaps% "1,0,1,0,0,0,1,1,0,0,0,0,4,0,1,0,0,3,2,0,1,0,0,1,2,0,0,0,1,1,3,2,0,0,0,0,0,3,0,0,1,1,3,0,5,0,0,0,1,0,0,1,1,1,0,1,1,1,0,0,1,0,0,1,1,2,0,1,0,0,2,0,0,0,1,0,7,6,0,1,2,0,0,0,0,2,2,2,1,0,3,0,1,0,2,0,0,0,1,1,0,0,0,0,4,0,0,0,1,0,0,4,0,2,3,0,0,0,4,0,2,4,0,0,0,0,1,5" [left030Row7Part5]

private noncomputable def left030Row7Part3 : List ℕ := native_gaps% "1,4,0,0,0,1,1,3,1,2,0,0,0,1,2,0,1,1,0,1,0,1,1,1,1,0,1,1,0,0,0,1,0,2,0,1,2,1,1,0,1,1,0,1,0,2,2,0,0,0,1,1,0,2,1,0,0,3,0,0,0,0,6,1,0,0,0,0,0,0,2,3,0,1,0,1,0,0,1,0,0,2,1,0,0,0,1,5,0,1,2,1,4,3,0,1,1,0,1,0,3,0,6,0,0,1,4,0,0,4,0,1,1,0,0,6,0,0,2,1,0,0,1,0,4,2,0,1" [left030Row7Part4]

private noncomputable def left030Row7Part2 : List ℕ := native_gaps% "1,0,0,0,2,0,1,1,1,1,0,0,3,0,1,0,3,3,0,0,2,0,2,0,1,0,1,0,0,2,4,0,2,2,0,2,0,0,0,0,0,0,0,1,0,2,2,1,0,4,1,0,4,0,0,0,0,4,1,2,3,0,0,0,0,1,0,1,1,0,1,0,0,0,0,0,0,3,0,2,0,3,0,3,2,0,3,1,0,1,2,0,2,0,0,0,4,5,1,0,3,2,1,4,2,0,0,0,0,0,0,0,0,1,1,2,2,0,0,0,0,0,1,1,1,0,1,3" [left030Row7Part3]

private noncomputable def left030Row7Part1 : List ℕ := native_gaps% "5,0,1,0,0,0,1,0,2,6,6,2,1,1,2,2,0,0,0,0,0,0,2,3,0,1,0,0,0,2,0,0,1,2,0,0,0,2,1,0,0,0,3,1,1,0,0,0,1,1,0,1,6,1,2,0,5,4,1,0,0,3,8,4,0,0,1,0,0,2,1,3,0,0,0,1,2,5,0,0,0,0,0,0,0,1,2,2,0,2,1,0,0,2,0,1,0,0,1,0,1,0,0,0,1,0,0,0,2,0,0,3,0,1,1,0,2,0,2,1,1,0,0,1,0,0,0,0" [left030Row7Part2]

private noncomputable def left030Row7Part0 : List ℕ := native_gaps% "4,1,1,0,2,0,2,3,1,1,0,2,1,0,0,1,0,0,1,0,0,0,0,0,1,1,1,4,0,0,1,0,1,0,0,1,1,0,0,1,0,1,0,0,2,0,0,0,0,1,0,1,0,0,6,0,1,2,0,4,0,5,0,1,1,0,4,1,77,0,21,3,2,1,1,1,4,2,2,0,0,0,0,1,0,2,2,0,1,1,0,0,0,1,3,0,1,0,1,2,1,0,0,0,2,0,1,2,3,2,1,3,1,1,1,1,1,0,0,0,0,1,2,0,4,0,1,1" [left030Row7Part1]

private noncomputable def left030Row7 : List ℕ := left030Row7Part0

private noncomputable def leftGaps030 : List (List ℕ) := [left030Row0, left030Row1, left030Row2, left030Row3, left030Row4, left030Row5, left030Row6, left030Row7]

private noncomputable def right030Row0Part5 : List ℕ := native_gaps% "1" [[]]

private noncomputable def right030Row0Part4 : List ℕ := native_gaps% "4,0,0,1,0,1,1,0,1,0,3,0,1,0,0,1,0,6,2,1,1,0,2,1,0,0,1,4,0,2,2,1,2,1,0,0,1,0,0,0,2,0,2,0,1,0,0,2,0,0,1,1,1,0,2,0,3,3,1,0,1,0,5,0,0,0,0,1,1,1,0,0,0,0,3,0,0,0,0,0,1,0,0,2,0,2,1,1,0,0,0,1,1,3,1,1,0,0,0,0,0,0,0,0,1,0,0,1,0,2,0,0,0,0,0,0,0,0,1,2,0,0,0,0,3,1,1,0" [right030Row0Part5]

private noncomputable def right030Row0Part3 : List ℕ := native_gaps% "0,1,0,0,0,0,0,0,1,0,0,1,0,2,2,0,1,0,1,0,0,1,0,0,6,0,2,1,0,2,5,7,0,0,2,0,2,0,2,0,2,0,0,1,0,3,1,0,0,0,4,0,3,0,0,0,1,14,0,2,0,0,2,0,2,3,0,0,0,0,0,1,0,0,0,2,1,0,2,3,0,1,2,0,0,2,0,2,1,0,2,0,0,2,0,3,3,3,0,0,0,0,0,1,1,1,0,0,1,0,0,1,0,0,2,4,0,0,0,1,3,0,1,1,1,0,0,0" [right030Row0Part4]

private noncomputable def right030Row0Part2 : List ℕ := native_gaps% "2,0,0,0,0,4,0,0,5,1,0,0,0,0,1,1,0,0,2,3,0,0,1,1,0,0,0,1,1,0,0,0,0,1,0,4,0,1,0,0,2,0,0,2,0,1,1,0,2,1,0,0,1,2,4,2,0,0,1,2,0,1,2,2,2,4,0,4,0,0,1,3,0,1,0,0,1,3,0,0,0,0,1,0,0,1,1,1,2,0,0,0,0,1,3,0,0,0,0,2,1,0,0,0,1,6,3,5,0,2,1,0,1,1,2,1,1,1,4,0,0,3,1,0,0,3,0,2" [right030Row0Part3]

private noncomputable def right030Row0Part1 : List ℕ := native_gaps% "0,1,3,3,1,1,2,0,1,1,0,0,1,1,3,0,0,0,0,0,2,0,1,1,0,0,0,0,0,0,0,1,0,0,0,3,0,1,0,0,0,4,0,0,3,1,1,0,0,0,2,0,1,0,0,1,2,0,1,0,3,0,0,1,0,0,1,2,2,2,1,6,0,0,1,1,1,0,1,0,2,0,0,0,2,0,2,3,0,2,0,2,0,2,1,2,1,0,0,1,0,0,3,4,1,1,1,0,1,0,0,0,0,2,1,1,0,1,1,1,1,1,2,2,3,0,3,3" [right030Row0Part2]

private noncomputable def right030Row0Part0 : List ℕ := native_gaps% "0,0,1,0,0,0,1,2,3,2,0,4,1,0,3,0,0,0,0,0,0,2,2,1,0,0,0,0,1,1,0,3,0,1,2,4,1,0,1,1,0,5,0,1,1,0,0,1,0,0,0,0,2,0,2,1,0,1,2,0,2,0,0,1,0,0,0,0,0,0,1,3,1,1,5,0,0,0,0,1,0,0,0,0,3,0,0,1,0,3,4,1,0,0,5,0,2,0,2,0,3,0,2,1,1,1,1,1,4,1,3,3,0,0,5,5,0,0,2,0,4,0,3,0,0,0,0,5" [right030Row0Part1]

private noncomputable def right030Row0 : List ℕ := right030Row0Part0

private noncomputable def right030Row1Part4 : List ℕ := native_gaps% "2,0,2,0,0,1,0,0,0,0,0,0,0,0,9,1,4,0,1,1,0,0,1,0,0,2,1,0,0,0,0,1,1,5,0,0,1,5,3,2,1,1,0,0,0,0,1,0,0,3,2,0,1,3,0,3,1,0,0,0,1,2,0,7,0,2,1,4,5,1,0,2,4,0,0,0,0,2,1,6,3,0,1,0,2,4,2,0,4,0,6,1,2,2,0,3,1,5,0,1,2,0,1,1,0,2,0,0,0,0" [[]]

private noncomputable def right030Row1Part3 : List ℕ := native_gaps% "5,0,0,1,0,0,2,0,0,1,0,0,0,1,1,0,2,2,1,2,0,0,0,0,0,2,0,0,1,1,2,0,0,0,0,0,0,0,3,2,1,5,1,0,1,1,2,0,1,4,0,0,1,1,0,2,0,0,0,0,4,1,5,4,0,3,1,1,1,1,6,2,0,0,0,4,0,3,0,0,0,0,0,1,1,0,1,3,1,2,0,0,0,6,0,0,3,1,0,0,0,0,3,2,1,0,0,0,1,0,2,2,0,0,3,3,1,1,1,1,1,2,0,1,2,0,0,0" [right030Row1Part4]

private noncomputable def right030Row1Part2 : List ℕ := native_gaps% "4,0,2,0,0,2,0,0,0,0,1,0,0,0,0,0,2,0,0,0,1,2,0,4,1,1,0,2,0,7,1,8,0,2,0,0,1,1,3,1,3,6,2,0,1,0,3,0,1,1,0,1,1,1,1,1,0,0,0,0,1,1,0,2,0,1,0,0,0,1,6,1,0,2,2,0,4,0,0,0,1,0,1,0,0,0,0,1,2,0,2,1,0,0,0,2,0,1,1,0,6,0,0,1,1,0,0,2,0,0,1,1,0,0,0,1,0,1,5,0,0,1,0,0,0,0,0,0" [right030Row1Part3]

private noncomputable def right030Row1Part1 : List ℕ := native_gaps% "0,0,0,3,7,0,0,1,0,1,0,1,2,0,0,0,2,0,0,1,3,0,2,3,0,0,2,0,0,0,0,0,0,0,0,2,0,0,2,0,0,0,0,6,0,5,0,0,0,0,6,0,0,0,0,5,0,2,0,0,0,1,0,1,3,1,0,2,2,0,3,0,1,1,0,0,1,1,1,2,1,3,0,2,1,1,1,0,0,0,2,3,0,0,0,0,4,1,3,2,3,1,0,0,0,1,0,1,1,3,2,1,0,0,0,0,0,5,0,1,0,1,0,0,1,0,0,0" [right030Row1Part2]

private noncomputable def right030Row1Part0 : List ℕ := native_gaps% "0,1,0,0,0,0,1,1,0,1,3,0,0,2,1,1,2,5,0,0,1,0,0,0,6,1,2,2,1,1,0,0,0,1,2,2,1,0,0,0,2,0,0,2,1,1,2,0,0,0,0,0,1,1,0,0,0,0,0,3,1,0,0,0,0,0,2,3,0,0,1,1,0,0,0,0,0,0,0,1,2,0,0,1,0,1,0,1,0,0,1,0,2,0,0,1,0,0,0,0,0,0,5,5,0,0,0,1,0,0,1,2,3,5,0,0,1,4,1,0,0,1,1,0,1,1,0,6" [right030Row1Part1]

private noncomputable def right030Row1 : List ℕ := right030Row1Part0

private noncomputable def right030Row2Part4 : List ℕ := native_gaps% "0,0,1,0,0,2,0,1,0,5,0,0,0,1,1,0,0,3,1,0,1,1,0,0,0,2,0,1,0,1,1,0,3,2,3,0,4,1,1,0,0,1,0,0,3,0,1,2,0,1,2,3,0,4,2,0,0,1,0,1,0,1,0,1,1,3,1,0,0,0,0,0,0,0,0,0" [[]]

private noncomputable def right030Row2Part3 : List ℕ := native_gaps% "1,0,2,0,2,3,1,0,1,0,2,1,4,7,0,0,1,2,0,1,0,1,0,0,5,2,1,1,0,0,1,5,1,2,0,0,0,0,1,5,3,0,2,1,5,0,1,6,2,2,3,0,0,0,1,2,0,2,1,1,1,1,1,3,1,0,0,4,0,3,1,0,3,0,1,0,3,0,0,4,1,0,1,2,1,2,1,2,0,0,1,0,4,2,0,2,1,1,1,4,0,0,1,4,0,0,0,0,2,1,0,0,2,1,0,0,2,0,1,0,0,4,2,2,1,3,0,0" [right030Row2Part4]

private noncomputable def right030Row2Part2 : List ℕ := native_gaps% "1,1,4,1,2,0,1,1,0,0,1,1,1,0,4,4,0,0,3,0,0,0,0,3,0,2,0,5,6,0,0,0,1,0,4,3,1,0,0,0,1,0,4,5,1,2,0,1,0,1,1,0,0,0,0,2,0,0,1,1,0,0,2,0,1,0,0,0,0,0,0,0,0,0,1,5,0,0,0,0,4,0,1,2,7,0,1,0,1,6,0,0,0,0,0,0,1,0,1,3,3,0,0,2,3,1,0,2,4,2,0,0,0,0,3,4,0,0,2,1,0,2,4,2,0,4,2,1" [right030Row2Part3]

private noncomputable def right030Row2Part1 : List ℕ := native_gaps% "1,1,1,3,2,0,2,0,0,1,1,0,1,0,0,1,0,0,0,2,4,1,0,0,3,0,1,0,0,0,1,0,0,0,2,2,2,0,0,0,1,0,0,1,1,1,1,1,0,0,0,2,1,0,2,0,0,0,0,5,1,0,1,0,2,1,0,1,0,1,1,3,0,1,0,7,0,0,5,0,0,0,4,0,1,3,2,0,0,0,0,2,0,0,1,0,2,4,1,0,0,0,0,0,1,3,0,0,0,0,0,2,5,1,1,2,0,3,8,1,0,0,0,0,0,1,0,0" [right030Row2Part2]

private noncomputable def right030Row2Part0 : List ℕ := native_gaps% "4,1,0,2,3,0,0,1,0,1,3,0,2,0,0,0,2,0,1,1,2,0,3,0,0,2,0,0,1,1,0,1,0,4,1,1,3,1,3,1,0,0,5,3,0,0,1,2,0,0,0,0,1,2,2,6,0,0,2,2,0,1,1,0,0,3,2,0,0,4,0,2,0,9,1,1,0,5,2,1,1,0,1,1,1,3,0,1,5,0,0,0,0,0,1,1,0,1,0,0,0,4,2,1,3,1,1,1,6,2,0,1,1,0,1,1,1,0,0,2,0,0,0,7,2,1,1,0" [right030Row2Part1]

private noncomputable def right030Row2 : List ℕ := right030Row2Part0

private noncomputable def right030Row3Part5 : List ℕ := native_gaps% "0,0,1,5,2,4,0,0,0" [[]]

private noncomputable def right030Row3Part4 : List ℕ := native_gaps% "0,3,1,3,0,0,0,2,1,2,1,0,0,0,5,1,1,0,1,1,11,5,1,0,0,1,0,0,0,0,2,0,1,0,3,0,1,0,0,1,0,0,0,2,3,0,0,0,0,0,2,0,0,0,0,1,1,2,0,1,0,0,0,1,0,1,2,0,3,0,1,0,1,0,1,0,1,3,2,0,1,4,2,2,0,0,1,0,0,0,0,1,0,0,0,1,1,1,1,1,0,1,1,2,0,1,0,2,2,2,3,0,2,0,1,0,0,0,2,1,1,5,1,0,2,0,0,2" [right030Row3Part5]

private noncomputable def right030Row3Part3 : List ℕ := native_gaps% "1,0,0,5,1,0,1,0,1,0,0,0,0,1,0,1,1,0,0,0,3,2,5,0,1,4,0,1,0,1,3,1,0,1,0,0,3,4,0,3,3,2,0,2,1,2,0,0,1,0,0,1,0,1,0,0,0,2,0,1,0,0,2,0,2,0,0,1,0,0,0,2,1,0,0,2,0,0,2,0,2,0,1,1,0,1,1,1,4,0,3,0,0,0,2,0,2,1,0,0,2,4,0,3,0,0,2,0,3,1,0,3,0,2,0,4,1,0,0,3,0,1,0,0,0,0,0,0" [right030Row3Part4]

private noncomputable def right030Row3Part2 : List ℕ := native_gaps% "0,0,2,1,0,2,0,2,2,0,1,1,1,0,0,1,0,0,2,0,0,2,2,0,0,0,1,0,1,0,4,0,2,1,7,1,0,1,0,1,0,0,0,3,0,0,1,3,1,0,3,1,0,3,0,0,5,0,0,1,0,1,0,1,0,0,3,0,0,0,0,2,1,0,1,1,1,0,1,5,0,0,2,0,2,0,1,1,1,1,0,1,1,1,1,4,0,0,0,1,2,3,2,0,0,0,2,1,0,1,0,0,1,1,0,0,0,0,0,1,0,0,0,1,1,1,0,2" [right030Row3Part3]

private noncomputable def right030Row3Part1 : List ℕ := native_gaps% "0,0,1,1,1,0,4,0,1,0,1,0,0,0,0,1,0,0,1,0,1,0,0,0,1,0,3,1,0,0,1,0,4,0,0,0,2,0,0,0,1,1,0,0,0,1,2,0,1,3,0,1,0,0,0,1,2,1,0,3,4,1,2,0,4,2,0,0,2,2,0,0,0,3,4,2,0,2,0,0,0,2,0,0,0,0,0,0,0,6,1,0,0,1,0,1,3,0,0,0,1,1,0,0,0,0,1,2,1,1,2,0,1,1,3,3,0,1,1,0,0,0,0,0,1,0,0,0" [right030Row3Part2]

private noncomputable def right030Row3Part0 : List ℕ := native_gaps% "0,4,0,2,1,0,0,0,2,0,0,3,0,1,0,0,1,4,0,1,2,2,2,0,1,1,0,0,6,0,0,1,0,0,0,2,0,5,0,2,1,2,0,3,3,1,0,3,0,2,3,1,0,0,0,2,0,4,4,1,0,1,0,0,0,0,0,2,1,0,1,2,1,0,0,0,0,0,1,4,0,0,0,0,2,0,2,0,0,1,0,1,0,1,0,4,0,0,1,0,2,0,0,0,2,5,1,3,0,0,0,1,1,1,1,1,2,0,0,0,0,0,4,0,0,0,1,0" [right030Row3Part1]

private noncomputable def right030Row3 : List ℕ := right030Row3Part0

private noncomputable def right030Row4Part4 : List ℕ := native_gaps% "0,0,0,0,3,0,0,1,4,0,0,3,1,1,0,2,1,0,1,0,1,1,2,1,1,1,5,0,1,0,0,0,0,0,0,0,0,0,4,1,1,3,0,0,0,0,0,0,1,0,0,1,2,0,0,0,3,0,3,1,1,0,1,0,0,1,0,2,3,2,1,0,0,1,1,0,1,0,0,3,0,3,1,3,0,5,0,3,3,0,3,1,0,0,0,0,0,2,1,2,1,3,0,0,0,2,2,9,0,0,0,1,0,0" [[]]

private noncomputable def right030Row4Part3 : List ℕ := native_gaps% "0,0,0,3,1,0,2,1,1,0,0,3,1,1,1,3,1,0,1,0,3,0,4,0,2,2,0,0,1,2,0,0,0,0,0,1,0,3,0,0,2,2,0,2,1,0,0,3,0,7,2,0,2,0,0,1,2,1,2,2,0,0,1,0,2,2,1,0,3,0,0,0,0,0,1,0,0,0,1,1,0,1,1,1,0,2,1,0,4,0,1,3,1,1,0,2,1,2,0,0,2,0,0,3,0,1,2,3,0,0,0,0,2,2,3,0,1,0,1,0,1,0,0,0,0,1,0,0" [right030Row4Part4]

private noncomputable def right030Row4Part2 : List ℕ := native_gaps% "3,0,0,0,0,1,1,1,0,2,0,0,3,3,0,3,2,0,0,0,0,0,0,2,0,1,2,1,0,0,4,1,1,2,0,3,2,0,1,6,0,1,4,0,0,2,0,2,1,0,0,1,3,0,3,0,2,0,0,0,3,0,0,0,1,1,1,0,1,3,0,4,1,1,0,0,0,2,2,2,0,0,0,1,1,2,0,2,1,2,0,4,0,1,1,1,0,0,1,0,2,0,1,2,0,3,1,0,0,1,0,1,1,2,1,0,1,0,5,2,0,7,0,1,1,3,1,3" [right030Row4Part3]

private noncomputable def right030Row4Part1 : List ℕ := native_gaps% "2,2,1,1,1,1,1,0,2,0,0,0,1,1,2,1,0,1,0,1,1,0,0,1,1,0,1,2,0,4,0,0,0,0,0,15,1,0,0,1,2,0,2,1,2,2,0,0,0,2,0,1,0,0,0,1,0,4,2,0,0,0,0,1,1,1,0,2,0,1,0,2,0,1,0,0,0,0,0,1,0,1,0,2,0,5,0,0,0,1,0,0,1,6,4,0,2,0,0,1,0,0,1,1,0,0,0,7,0,1,0,0,0,0,6,3,0,0,1,2,1,1,0,1,0,1,0,1" [right030Row4Part2]

private noncomputable def right030Row4Part0 : List ℕ := native_gaps% "2,1,0,0,1,2,0,0,1,0,1,0,1,0,2,2,0,2,4,0,0,0,1,1,0,1,0,0,2,0,0,2,1,0,0,0,2,0,2,3,0,1,1,6,0,1,4,2,0,2,0,0,1,6,0,1,1,3,0,1,0,0,2,0,0,0,2,0,1,0,0,1,1,1,0,1,1,0,1,1,2,2,0,1,1,0,2,1,0,0,8,0,0,2,2,1,0,0,1,0,0,0,0,3,1,0,1,0,0,0,0,0,3,0,0,2,1,0,2,0,1,0,3,0,0,1,0,0" [right030Row4Part1]

private noncomputable def right030Row4 : List ℕ := right030Row4Part0

private noncomputable def right030Row5Part4 : List ℕ := native_gaps% "3,9,0,0,1,0,3,4,3,1,0,1,0,0,0,0,0,2,0,1,0,1,0,0,2,0,0,0,0,0,2,1,1,4,0,1,0,1,3,0,1,2,0,3,0,0,3,9,0,1,2,0,2,2,1,0,1,0,0,2,1,0,0,0,0,3,0,0,0,0,0,0,1,4,3,0,0,0,1,4,0,1,0,0,0,0,0,3,2,0,0,0,0,0,0,5,2,2,0" [[]]

private noncomputable def right030Row5Part3 : List ℕ := native_gaps% "0,0,1,3,5,1,0,0,1,2,3,0,2,0,0,3,1,3,1,4,0,0,0,1,1,1,6,0,6,1,0,0,3,0,4,1,0,1,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,0,0,0,1,0,1,1,2,1,1,0,0,1,1,1,0,0,2,2,1,4,0,0,0,6,0,2,0,2,0,0,0,2,0,0,1,0,1,0,3,1,0,2,4,0,1,1,1,0,0,1,0,5,0,0,0,2,0,4,0,0,1,0,0,1,0,0,1,1,1,2,0,1,0,5" [right030Row5Part4]

private noncomputable def right030Row5Part2 : List ℕ := native_gaps% "1,6,0,1,1,0,2,0,0,0,1,0,0,2,1,0,1,0,0,0,3,1,1,1,0,0,1,0,2,1,1,0,1,0,0,2,0,0,3,1,2,0,3,0,2,2,1,1,0,5,1,0,2,4,2,1,4,0,0,6,4,0,0,0,0,2,1,0,0,1,0,0,3,3,1,0,0,0,0,0,3,3,0,0,0,0,4,0,2,1,0,0,0,4,2,0,1,0,0,3,3,0,0,4,0,0,1,1,0,6,1,4,4,0,1,1,1,0,0,0,0,1,6,2,0,0,2,0" [right030Row5Part3]

private noncomputable def right030Row5Part1 : List ℕ := native_gaps% "1,0,1,0,2,1,3,0,0,1,0,1,0,0,1,1,2,0,1,0,0,1,0,1,2,5,0,4,0,0,1,2,0,0,1,2,0,0,3,0,0,3,0,2,0,0,10,0,0,0,0,1,2,0,1,1,3,0,0,0,0,0,0,2,2,2,1,1,1,0,1,0,0,1,1,2,1,1,0,2,2,0,2,2,4,1,0,1,2,0,1,2,0,0,1,0,0,0,0,5,2,2,1,0,1,0,0,1,1,0,0,1,1,0,1,2,0,2,3,1,0,0,2,0,0,0,2,2" [right030Row5Part2]

private noncomputable def right030Row5Part0 : List ℕ := native_gaps% "2,0,0,0,0,0,1,0,1,1,0,1,0,3,4,0,0,0,2,3,0,1,1,2,2,4,2,1,0,0,0,1,0,2,0,1,2,2,1,4,0,0,0,0,0,1,0,2,5,0,1,0,0,1,1,1,1,2,2,1,4,2,0,1,1,0,0,1,0,0,0,0,1,2,1,1,0,3,2,3,1,0,1,0,3,1,0,0,0,1,0,0,3,0,0,0,0,0,3,1,6,0,0,0,1,2,0,3,0,1,0,1,0,1,0,1,1,0,0,1,1,0,0,0,0,0,0,0" [right030Row5Part1]

private noncomputable def right030Row5 : List ℕ := right030Row5Part0

private noncomputable def right030Row6Part4 : List ℕ := native_gaps% "3,4,0,4,0,2,1,0,1,0,0,0,0,1,1,3,0,1,0,0,0,1,0,8,0,0,0,0,3,0,0,0,0,0,0,2,0,0,1,0,0,1,5,1,0,0,0,1,2,0,1,0,2,1,4,0,0,0,0,0,4,0,0,1,3,0,1,1,0,0,5,3,0,1,0,1,0,2,0,5,2,1,0,1,2,0,0,1,3,3,1,0,0,0,1,0,1" [[]]

private noncomputable def right030Row6Part3 : List ℕ := native_gaps% "1,1,0,0,0,1,1,1,2,0,0,2,0,0,2,0,1,1,0,2,1,1,1,0,2,1,0,0,0,4,0,1,1,0,1,2,2,1,2,0,0,0,2,1,0,0,5,1,0,3,3,9,0,4,2,0,0,0,2,0,1,1,0,6,3,2,0,1,3,0,2,0,0,1,0,2,1,1,0,0,0,0,0,3,0,0,0,0,0,0,0,5,0,0,1,0,1,4,3,0,1,2,3,2,0,4,1,0,0,0,5,0,1,0,0,2,0,0,3,1,0,1,0,0,0,2,4,0" [right030Row6Part4]

private noncomputable def right030Row6Part2 : List ℕ := native_gaps% "0,0,1,1,1,0,0,1,0,0,2,3,2,1,1,0,1,1,3,1,0,0,1,1,1,2,0,1,3,0,3,1,1,3,0,0,5,1,0,1,0,1,0,1,0,1,4,2,4,0,0,2,0,1,0,1,0,0,0,0,0,2,0,1,0,0,1,0,2,0,0,0,1,1,1,1,1,6,0,1,0,0,1,0,0,1,1,1,0,0,1,1,1,1,0,2,2,0,1,3,0,8,0,1,0,2,0,2,0,0,0,0,0,1,0,0,0,3,3,1,7,0,0,0,3,1,1,1" [right030Row6Part3]

private noncomputable def right030Row6Part1 : List ℕ := native_gaps% "0,0,0,0,2,1,0,1,0,0,0,2,1,4,0,0,1,0,0,4,0,3,4,2,1,0,1,0,0,0,0,5,1,0,0,0,1,2,0,0,3,0,3,0,0,1,0,1,0,0,1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,0,0,4,1,2,0,1,0,1,2,3,3,2,0,0,0,0,0,0,3,1,3,6,6,2,1,1,1,1,0,0,0,0,1,2,3,6,9,0,4,0,1,3,2,0,0,0,2,0,1,4,2,1,0,1,0,5,1,0,0" [right030Row6Part2]

private noncomputable def right030Row6Part0 : List ℕ := native_gaps% "1,1,0,2,1,0,0,0,0,0,6,5,2,0,1,1,0,0,1,0,0,1,1,1,1,0,0,1,2,0,0,3,0,1,0,1,1,0,0,1,1,0,1,0,1,1,3,4,4,0,6,1,2,0,0,1,0,0,5,0,1,0,0,0,1,2,1,3,1,0,2,1,0,0,0,1,0,0,0,1,0,0,0,1,0,2,0,0,2,0,0,0,1,0,0,2,0,0,1,0,5,0,1,1,1,0,1,5,0,6,0,0,1,0,0,0,1,1,2,2,1,0,0,0,3,0,2,1" [right030Row6Part1]

private noncomputable def right030Row6 : List ℕ := right030Row6Part0

private noncomputable def right030Row7Part4 : List ℕ := native_gaps% "0,0,1,0,0,3,1,0,0,0,1,0,1,0,1,2,2,2,0,1,1,0,3,0,3,0,2,0,2,3,1,1,5,2,1,0,0,0,0,0,2,1,0,2,0,1,0,2,0,2,0,1,0,0,4,0,0,1,2,2,0,4,0,2,0,1,0,0,4,0,0,0,2,0,1,0,1,0,2,0,1,0,0,1,1" [[]]

private noncomputable def right030Row7Part3 : List ℕ := native_gaps% "0,0,1,0,3,1,5,1,2,0,0,0,2,0,1,1,1,3,2,2,0,0,1,0,4,1,2,0,2,0,0,0,2,2,3,1,1,2,6,1,1,0,0,0,0,0,0,1,0,2,1,0,0,0,0,0,1,3,0,0,2,2,1,0,1,1,0,5,2,5,0,0,0,0,0,1,0,0,0,0,2,0,2,0,1,0,0,0,0,0,2,0,1,0,0,0,1,1,0,0,1,0,1,0,0,0,1,0,1,0,0,7,0,1,1,2,0,0,0,0,1,0,3,2,0,2,0,2" [right030Row7Part4]

private noncomputable def right030Row7Part2 : List ℕ := native_gaps% "0,2,1,1,1,0,4,0,1,0,0,0,0,0,5,3,3,0,0,0,3,2,1,4,0,0,0,0,1,1,0,1,0,0,2,0,1,0,2,0,5,0,1,0,2,2,3,2,1,1,1,5,2,7,0,0,0,2,1,0,2,0,4,3,1,0,0,4,0,1,0,0,1,0,0,0,1,6,2,1,11,0,1,0,2,0,9,3,0,0,3,0,1,2,9,2,0,0,3,4,2,1,0,1,0,0,1,0,4,1,3,1,5,1,1,2,1,0,0,0,0,0,0,6,1,1,0,2" [right030Row7Part3]

private noncomputable def right030Row7Part1 : List ℕ := native_gaps% "0,1,1,0,0,0,2,0,3,0,0,3,0,0,1,0,0,1,2,1,4,0,0,1,0,1,2,2,0,3,2,0,0,2,1,1,0,4,0,0,2,0,2,1,0,5,3,1,0,1,0,1,3,0,0,0,1,2,1,3,1,0,0,0,0,0,2,0,6,1,4,0,0,0,1,0,0,1,8,0,1,2,0,1,3,1,0,0,0,1,0,0,3,4,0,0,2,0,0,1,0,0,1,1,0,0,0,0,2,3,0,0,1,2,0,0,0,0,0,0,1,0,2,1,0,1,2,2" [right030Row7Part2]

private noncomputable def right030Row7Part0 : List ℕ := native_gaps% "1,0,0,0,1,4,1,1,0,0,0,2,5,0,2,3,0,3,1,0,1,2,2,0,0,0,2,1,0,3,6,1,0,1,0,0,2,0,0,4,0,0,1,2,4,1,0,0,2,0,0,0,0,0,4,3,0,1,0,2,0,0,0,0,0,0,1,3,4,0,3,0,4,1,1,2,1,1,3,0,0,5,2,1,1,1,0,0,1,0,0,0,1,0,1,0,0,0,0,0,3,1,0,0,0,0,0,1,6,5,1,2,0,0,0,0,0,3,1,1,0,0,0,0,0,5,2,0" [right030Row7Part1]

private noncomputable def right030Row7 : List ℕ := right030Row7Part0

private noncomputable def rightGaps030 : List (List ℕ) := [right030Row0, right030Row1, right030Row2, right030Row3, right030Row4, right030Row5, right030Row6, right030Row7]

private theorem leftMask030 :
    (leftGaps030.map gapMask == (sourceTransposeA.drop 240).take 8) = true := by
  decide +kernel

private theorem rightMask030 :
    (rightGaps030.map gapMask == (quotientTransposeRows.drop 240).take 8) = true := by
  decide +kernel

private theorem products030 :
    (leftGaps030.map (gapRow quotientTransposeRows) == rightGaps030.map (gapRow targetA)) = true := by
  decide +kernel

theorem block030 :
    checkEqualProducts quotientTransposeRows targetA
      ((sourceTransposeA.drop 240).take 8) ((quotientTransposeRows.drop 240).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask030) (beq_iff_eq.mp rightMask030)
    (beq_iff_eq.mp products030)

private noncomputable def left031Row0Part5 : List ℕ := native_gaps% "3,1,2,2,0,1,3,6,0,0,0,4,2" [[]]

private noncomputable def left031Row0Part4 : List ℕ := native_gaps% "0,0,0,0,0,1,0,1,0,0,3,1,0,0,0,1,2,0,0,0,0,0,2,2,0,0,3,0,0,1,0,1,1,0,1,1,0,2,2,6,0,0,0,3,0,0,0,0,0,0,0,0,1,0,0,2,4,1,0,0,1,2,3,4,7,1,0,2,4,1,0,2,1,0,0,0,0,3,0,0,0,0,3,1,1,0,1,1,0,0,2,4,1,0,2,0,1,1,0,1,2,0,1,3,0,4,1,2,0,0,3,0,0,0,0,3,0,0,0,2,0,3,5,0,0,2,0,2" [left031Row0Part5]

private noncomputable def left031Row0Part3 : List ℕ := native_gaps% "1,0,0,1,0,3,0,2,3,1,0,0,2,0,1,0,2,1,2,2,1,2,5,1,0,0,0,2,1,0,3,1,1,0,2,3,0,1,2,0,2,4,0,3,1,0,3,0,0,3,3,3,1,1,0,1,1,3,1,0,0,1,0,0,0,7,0,3,2,0,0,3,6,5,1,1,1,1,1,4,1,0,0,5,1,1,1,0,1,0,1,1,1,1,0,0,0,1,1,0,4,0,1,1,2,1,0,0,0,0,5,0,2,0,5,2,0,2,1,1,2,0,0,1,1,0,0,0" [left031Row0Part4]

private noncomputable def left031Row0Part2 : List ℕ := native_gaps% "0,2,0,0,1,0,0,0,1,0,2,3,0,1,1,4,2,1,0,0,0,4,2,4,0,1,0,0,0,4,0,0,0,1,5,0,0,4,0,2,1,0,0,1,0,0,0,1,0,2,1,0,0,0,2,0,0,0,1,2,5,0,0,0,0,2,0,0,0,0,0,0,4,8,0,3,0,5,1,1,1,1,0,1,5,0,0,0,1,1,3,0,1,0,0,1,0,1,0,1,1,2,0,1,0,1,0,0,1,0,2,2,0,1,1,3,5,2,2,0,0,2,0,2,4,3,2,0" [left031Row0Part3]

private noncomputable def left031Row0Part1 : List ℕ := native_gaps% "0,2,1,0,2,0,0,0,1,6,5,0,4,0,2,3,1,0,0,0,2,6,0,0,0,0,3,0,1,3,0,0,0,0,0,4,0,1,3,3,0,0,0,1,0,3,1,3,1,1,0,2,5,0,1,1,1,0,1,0,1,0,2,1,0,0,2,0,0,0,0,0,1,0,0,3,0,0,2,1,0,0,2,3,0,1,0,0,1,2,1,0,2,1,0,1,0,1,2,5,3,0,0,3,2,0,1,1,0,2,2,0,2,1,0,2,0,0,0,1,1,0,0,0,2,0,0,1" [left031Row0Part2]

private noncomputable def left031Row0Part0 : List ℕ := native_gaps% "0,6,0,0,0,0,4,1,0,0,1,3,6,3,0,1,2,2,0,3,0,2,1,3,1,1,6,0,0,0,1,0,3,2,0,4,0,3,0,0,6,0,1,7,2,1,0,0,0,1,1,0,0,76,0,0,20,1,0,0,1,1,4,0,2,1,0,0,0,1,1,0,1,2,0,1,3,0,0,0,0,1,1,3,2,0,1,3,0,0,0,4,0,2,4,0,1,0,1,1,0,2,0,0,0,3,0,1,1,0,0,4,3,0,0,0,0,0,0,0,3,0,0,0,0,3,2,1" [left031Row0Part1]

private noncomputable def left031Row0 : List ℕ := left031Row0Part0

private noncomputable def left031Row1Part5 : List ℕ := native_gaps% "2,1,0,1,1,2,1,0,0,1,0,0,0,0,1,1,0,0,0,0,2,0,2,1,0,1,0,0,0,0" [[]]

private noncomputable def left031Row1Part4 : List ℕ := native_gaps% "0,0,0,2,0,0,0,0,0,2,0,2,0,0,0,2,1,1,0,0,1,1,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,4,2,2,0,2,0,0,0,0,2,0,1,1,3,2,0,0,0,0,1,1,0,1,2,0,1,4,1,0,2,0,1,0,0,0,0,6,6,1,1,1,0,1,4,1,1,2,1,0,0,10,1,0,2,1,0,4,1,0,1,0,0,3,1,0,2,0,1,0,1,0,0,0,2,0,1,2,2,1,0,0,0,7" [left031Row1Part5]

private noncomputable def left031Row1Part3 : List ℕ := native_gaps% "0,4,0,0,1,0,2,1,0,0,1,2,0,0,0,2,1,2,2,1,2,0,2,0,3,1,0,1,0,1,2,0,0,0,1,0,1,0,0,2,0,0,0,0,1,2,1,0,0,0,1,4,1,0,1,0,1,1,2,0,1,1,1,0,1,4,0,2,0,0,3,1,3,1,4,0,1,3,0,0,0,0,2,1,2,6,0,2,2,0,0,1,0,1,0,1,1,2,2,0,10,5,2,0,1,0,2,0,0,0,2,2,0,0,0,2,0,3,0,0,1,2,2,0,0,0,6,1" [left031Row1Part4]

private noncomputable def left031Row1Part2 : List ℕ := native_gaps% "0,2,0,0,0,0,2,1,2,0,2,2,0,0,1,1,1,0,0,4,0,0,1,2,1,0,5,3,0,0,1,2,0,0,0,0,2,0,0,4,1,0,1,3,0,0,1,1,1,0,1,0,0,3,0,0,0,0,1,0,0,0,0,2,1,0,0,4,0,0,0,2,2,0,0,0,0,0,1,0,1,2,3,1,1,0,0,3,1,2,0,2,0,0,1,0,0,1,1,3,0,2,0,2,5,0,0,2,2,2,0,2,1,2,2,1,2,3,1,1,0,1,0,1,1,1,1,2" [left031Row1Part3]

private noncomputable def left031Row1Part1 : List ℕ := native_gaps% "0,0,1,6,1,1,0,1,2,2,0,4,1,2,1,4,1,1,0,9,5,0,0,0,1,0,2,0,0,1,2,0,0,3,1,1,2,2,0,2,0,2,0,2,2,1,3,0,0,1,0,2,5,2,5,0,0,1,0,0,0,1,1,0,0,2,1,0,1,4,0,1,3,0,3,0,2,0,0,0,2,1,0,1,1,0,2,0,3,0,0,0,1,2,2,0,6,0,0,0,0,6,1,0,0,3,0,4,0,4,0,1,3,2,1,0,0,0,2,1,1,1,1,3,4,2,2,0" [left031Row1Part2]

private noncomputable def left031Row1Part0 : List ℕ := native_gaps% "0,1,2,0,0,1,1,1,1,2,0,0,0,0,1,0,1,5,0,0,3,0,0,1,0,1,0,1,0,3,9,0,1,0,0,0,0,2,0,1,1,1,1,1,1,1,2,0,2,0,3,1,0,4,1,2,0,1,0,0,0,2,0,0,1,0,0,0,76,2,21,0,1,0,2,1,1,0,1,0,3,2,0,2,2,1,0,0,2,0,2,2,0,5,2,1,4,2,4,0,1,6,1,3,0,0,4,0,3,0,0,3,0,1,1,0,0,0,0,2,3,2,0,3,1,0,3,0" [left031Row1Part1]

private noncomputable def left031Row1 : List ℕ := left031Row1Part0

private noncomputable def left031Row2Part5 : List ℕ := native_gaps% "1,5,1,0,0,4,2,0,0,0,5,1,0,0,1,0,3,0,1,1,0,0,0,1,1,2,1,2,1,2,3,1,0,3,2,0,1,5,2,0,4,0,0,3,1,1,1,0,6,0,0,3,3,0,1,4,2,0,1,0,2,2,0,0" [[]]

private noncomputable def left031Row2Part4 : List ℕ := native_gaps% "0,0,1,1,0,1,0,0,2,0,0,1,1,0,0,0,0,1,0,0,2,2,2,1,0,1,2,0,0,3,0,1,0,1,1,0,1,0,5,3,0,0,0,3,0,0,2,0,2,0,1,1,4,0,1,0,0,0,0,0,1,0,1,6,4,1,1,0,0,0,0,0,0,1,0,1,0,0,0,0,0,3,0,0,0,0,1,1,0,0,0,1,0,2,0,1,0,0,0,0,1,1,0,0,2,0,0,0,3,2,0,1,0,0,0,0,0,1,0,0,2,0,0,0,1,1,1,1" [left031Row2Part5]

private noncomputable def left031Row2Part3 : List ℕ := native_gaps% "0,0,1,2,1,4,2,0,2,0,0,2,0,3,2,0,3,0,0,0,2,1,2,0,1,1,0,0,0,5,0,0,2,0,0,0,3,0,0,1,0,3,0,3,0,1,1,3,2,0,2,3,3,0,0,2,2,1,0,0,0,1,0,0,1,0,2,0,0,1,2,0,0,0,2,1,3,0,1,2,0,0,3,1,0,2,0,1,0,3,0,4,1,3,0,0,0,0,1,0,1,0,0,4,1,1,4,2,0,0,0,3,0,1,2,1,4,0,1,2,3,0,1,0,0,0,0,0" [left031Row2Part4]

private noncomputable def left031Row2Part2 : List ℕ := native_gaps% "0,0,0,2,0,3,2,1,0,0,0,0,2,0,0,0,0,0,1,3,0,1,7,0,2,0,3,2,0,0,1,0,1,4,2,0,0,0,0,1,1,1,3,0,0,4,0,0,0,5,2,0,1,2,1,0,0,2,1,1,0,0,0,1,0,3,0,0,0,0,0,0,0,0,2,2,0,0,1,0,0,2,5,1,0,1,1,1,1,2,0,0,0,2,4,0,3,0,1,1,1,1,3,1,1,1,0,1,1,0,0,0,1,0,0,0,0,0,2,0,0,1,0,0,4,1,0,1" [left031Row2Part3]

private noncomputable def left031Row2Part1 : List ℕ := native_gaps% "4,0,0,0,1,0,2,0,1,1,2,1,0,2,1,0,0,0,1,2,3,0,2,0,0,0,0,0,0,0,0,0,0,1,0,0,1,2,0,0,1,1,2,1,1,1,0,0,1,0,2,3,0,0,1,2,1,2,0,0,0,1,0,0,2,1,1,1,1,1,0,0,0,3,0,3,0,0,0,3,1,3,2,0,1,1,0,3,3,1,1,0,0,4,0,2,0,1,4,0,1,3,0,2,1,0,2,2,3,2,4,1,0,1,0,0,1,0,3,0,0,0,2,0,1,0,3,0" [left031Row2Part2]

private noncomputable def left031Row2Part0 : List ℕ := native_gaps% "0,1,2,0,1,0,0,0,0,0,0,0,2,0,1,1,0,2,2,1,0,3,2,1,3,0,0,0,2,1,0,0,2,3,1,0,1,2,6,0,0,1,0,0,1,1,0,0,0,0,0,0,1,1,0,0,1,1,3,0,0,0,1,1,2,1,0,0,1,0,3,0,76,0,0,19,2,0,0,3,0,0,0,0,0,0,2,2,0,2,0,1,1,0,1,0,1,3,0,0,0,1,6,3,1,3,1,0,5,2,12,2,1,3,2,0,0,2,1,0,0,2,3,1,0,0,1,1" [left031Row2Part1]

private noncomputable def left031Row2 : List ℕ := left031Row2Part0

private noncomputable def left031Row3Part5 : List ℕ := native_gaps% "1,0,0,2,0,1,0,0,4,0,1,0,0,2,3,0,0,1,1,2,1,0,0,1,0,0,0,3,0,3,0,1,3,0,1,0,0,5,0,2,0,1,2,0,1,0,0,5,0,0,0,0" [[]]

private noncomputable def left031Row3Part4 : List ℕ := native_gaps% "0,0,0,0,0,3,0,0,2,0,0,0,0,0,0,2,1,3,3,0,0,1,0,1,0,0,2,0,3,1,1,1,2,0,0,0,0,1,0,0,0,6,0,1,7,2,1,0,0,0,1,2,0,0,0,0,0,0,1,1,0,3,3,0,0,2,0,1,0,0,0,2,0,1,1,0,0,0,2,2,0,0,0,1,1,2,0,0,3,0,0,3,0,3,7,0,4,1,5,2,0,0,0,0,1,2,2,7,0,0,0,4,0,0,0,1,0,0,1,1,0,2,2,4,2,3,1,2" [left031Row3Part5]

private noncomputable def left031Row3Part3 : List ℕ := native_gaps% "1,0,0,2,0,0,3,0,1,1,3,0,1,4,0,0,1,2,1,1,0,0,1,0,2,0,0,0,0,0,0,1,0,0,2,0,0,1,0,2,1,0,1,0,1,4,1,0,2,6,1,2,1,0,0,0,5,5,0,0,0,1,0,1,1,1,0,3,0,1,3,0,4,1,0,1,0,0,1,2,0,0,1,2,3,0,0,0,0,0,0,5,0,1,4,2,0,1,0,0,1,0,2,0,5,5,4,0,0,0,0,0,3,1,0,0,0,0,0,0,1,1,1,0,0,2,2,0" [left031Row3Part4]

private noncomputable def left031Row3Part2 : List ℕ := native_gaps% "0,2,1,0,0,1,0,1,0,1,1,0,2,0,3,3,1,0,5,0,1,0,0,0,4,0,0,3,0,1,0,4,1,1,1,2,0,0,1,3,0,1,0,0,0,0,0,0,0,1,0,1,3,1,0,1,1,0,1,3,0,2,3,1,1,1,1,0,0,1,5,0,2,1,5,3,0,0,0,0,0,4,0,0,2,1,0,2,2,0,1,0,4,4,0,0,5,0,3,0,3,1,1,0,1,0,1,0,0,0,3,0,3,0,0,5,2,2,0,1,1,2,0,4,1,0,0,1" [left031Row3Part3]

private noncomputable def left031Row3Part1 : List ℕ := native_gaps% "0,1,1,0,1,11,0,1,1,0,1,1,0,2,1,0,0,0,1,0,2,1,0,0,0,2,0,0,0,0,0,0,0,3,5,0,0,2,0,0,3,0,0,1,0,1,2,0,0,0,1,2,0,0,0,3,0,3,0,0,0,0,1,3,0,1,1,0,1,4,0,2,0,6,0,0,0,2,0,0,0,0,3,2,0,1,3,0,0,4,1,0,0,0,0,1,0,5,0,4,0,0,1,0,2,0,5,2,0,0,1,3,0,0,0,0,0,0,3,0,1,0,0,0,1,0,0,1" [left031Row3Part2]

private noncomputable def left031Row3Part0 : List ℕ := native_gaps% "0,0,2,0,1,0,1,0,0,1,0,2,2,2,2,0,0,2,0,0,0,0,0,3,3,0,1,0,1,0,2,0,3,0,0,1,0,3,3,0,0,0,0,4,4,1,0,0,0,2,0,2,0,0,0,0,0,0,1,0,0,2,0,2,2,1,0,0,0,2,1,77,0,0,19,0,1,0,0,0,0,1,0,0,0,0,1,0,2,0,0,0,2,0,1,2,0,0,0,0,0,1,0,2,0,0,1,1,3,0,1,14,1,6,0,1,0,2,5,0,2,2,0,2,1,2,2,0" [left031Row3Part1]

private noncomputable def left031Row3 : List ℕ := left031Row3Part0

private noncomputable def left031Row4Part5 : List ℕ := native_gaps% "1,7,0,0,0,1,1,2,0,2,7,0,0,1,1,0,0,2,0,0,0,1,1,1,1,0,0,0,0,2,1,1,1,0,0,0,1,1,0,3" [[]]

private noncomputable def left031Row4Part4 : List ℕ := native_gaps% "1,2,2,6,3,0,0,0,1,1,2,1,0,0,0,0,4,1,1,2,0,0,0,5,0,2,1,0,0,0,0,0,0,1,0,3,0,0,0,0,0,3,1,1,0,0,1,1,0,0,1,2,1,0,1,2,0,2,0,0,1,0,3,3,0,0,2,1,0,1,0,2,3,0,0,1,0,0,0,0,0,0,0,4,0,0,0,0,2,2,2,0,5,0,0,0,0,1,0,0,0,0,1,1,0,4,1,0,0,0,2,3,1,0,2,4,0,0,0,0,1,0,0,2,2,0,1,0" [left031Row4Part5]

private noncomputable def left031Row4Part3 : List ℕ := native_gaps% "1,1,2,0,0,3,1,0,0,0,2,2,2,0,1,0,0,0,1,0,2,0,1,0,1,6,6,0,0,0,0,2,1,0,2,1,1,0,0,0,0,0,0,0,1,0,0,0,1,1,0,2,0,0,0,0,0,0,0,1,0,0,1,0,0,1,3,2,1,1,2,1,0,0,0,3,1,0,1,3,0,0,1,1,1,1,0,2,5,2,1,2,4,0,0,0,0,0,0,0,2,1,0,0,1,0,2,0,0,1,1,1,0,0,0,2,0,0,0,0,1,1,0,0,1,4,1,1" [left031Row4Part4]

private noncomputable def left031Row4Part2 : List ℕ := native_gaps% "3,0,3,1,1,0,0,5,0,0,3,2,0,0,0,0,0,0,1,5,1,0,0,1,1,0,0,0,1,0,2,0,0,1,2,0,0,0,0,6,0,0,0,4,0,0,1,1,1,0,1,1,4,1,0,2,0,0,0,1,2,3,3,0,0,1,10,0,3,2,3,0,2,1,8,0,3,0,1,0,2,1,0,1,1,0,0,1,3,0,1,1,1,0,0,0,2,4,1,0,3,0,1,0,0,1,0,1,2,2,0,1,1,2,3,0,0,2,0,0,2,1,0,0,2,0,1,0" [left031Row4Part3]

private noncomputable def left031Row4Part1 : List ℕ := native_gaps% "0,3,1,0,2,0,3,3,0,2,2,0,1,0,0,4,0,0,0,0,0,0,3,0,0,0,0,1,1,11,0,3,0,0,3,0,5,0,4,0,4,0,0,2,1,0,1,0,0,2,0,1,1,0,0,0,0,5,2,2,1,0,0,1,0,2,1,0,1,0,0,0,0,0,0,0,2,1,0,1,1,1,0,1,2,1,0,2,1,0,3,4,2,1,0,0,3,0,4,1,7,2,1,1,3,0,1,1,0,1,2,0,0,2,1,0,0,1,0,0,0,0,1,0,0,8,1,1" [left031Row4Part2]

private noncomputable def left031Row4Part0 : List ℕ := native_gaps% "0,4,0,0,0,1,0,0,0,2,5,1,0,0,0,0,0,5,2,4,0,1,3,0,1,2,0,0,0,1,2,0,0,0,0,5,1,2,0,2,0,0,4,1,2,1,1,1,1,0,4,0,1,0,3,1,0,2,0,2,2,76,23,1,0,0,0,0,0,1,0,0,2,1,0,1,0,2,0,0,0,0,1,3,3,5,1,0,4,1,0,1,3,2,0,3,0,2,4,2,1,0,0,1,7,1,0,5,4,3,0,2,1,1,3,0,1,3,0,1,0,1,0,0,1,2,1,0" [left031Row4Part1]

private noncomputable def left031Row4 : List ℕ := left031Row4Part0

private noncomputable def left031Row5Part5 : List ℕ := native_gaps% "0,2,1,1,0,0,1,0,4,1,0,0,0,0,1,0,0,0,1,0,0,0,3,1,0,4,1,3,1,0,0,0,0,1,3,0,0,0,0,0,2,0,1,0" [[]]

private noncomputable def left031Row5Part4 : List ℕ := native_gaps% "3,2,0,4,0,1,1,1,0,1,0,4,0,0,1,0,0,2,1,0,4,0,0,0,1,0,0,1,1,2,0,0,0,4,0,1,0,3,1,0,3,1,1,1,0,0,0,1,1,1,0,0,0,2,0,1,0,0,1,2,1,0,0,0,3,1,0,1,0,0,1,2,3,1,0,3,0,0,1,1,0,2,5,5,0,1,1,0,0,1,4,0,0,0,1,1,1,0,0,0,0,1,2,0,1,1,0,0,3,2,0,0,3,0,1,0,2,4,0,5,0,0,1,0,2,3,1,5" [left031Row5Part5]

private noncomputable def left031Row5Part3 : List ℕ := native_gaps% "1,0,2,2,2,0,2,1,1,1,0,0,2,7,1,0,1,0,0,0,1,0,4,0,0,0,0,0,0,0,0,1,2,1,0,0,3,0,1,0,0,0,0,0,1,0,1,7,0,1,4,2,0,0,1,0,0,0,0,2,0,1,3,2,1,1,1,1,7,0,0,0,6,2,2,0,6,1,0,2,0,0,0,0,0,0,0,2,0,0,0,1,3,0,0,1,2,0,0,2,0,0,5,1,2,0,0,0,3,0,1,0,0,0,1,1,0,0,0,2,1,0,8,1,0,0,3,0" [left031Row5Part4]

private noncomputable def left031Row5Part2 : List ℕ := native_gaps% "0,0,1,1,3,0,0,0,0,1,2,0,1,3,0,0,0,2,0,0,1,3,4,2,2,0,3,0,1,1,0,0,4,0,0,2,0,7,1,2,1,1,0,0,0,0,0,2,4,2,0,1,4,4,3,1,0,0,0,1,0,2,0,1,4,3,0,1,0,0,1,0,0,2,1,0,1,0,1,0,1,1,0,0,1,0,1,2,0,1,0,0,1,1,1,1,0,1,0,1,3,0,3,2,0,1,0,0,0,3,2,3,1,0,0,2,0,2,2,2,0,1,1,3,2,1,0,2" [left031Row5Part3]

private noncomputable def left031Row5Part1 : List ℕ := native_gaps% "2,2,0,0,3,1,0,0,0,1,2,2,1,1,1,0,0,1,0,0,4,0,1,1,2,0,3,3,1,0,0,0,4,0,0,1,3,0,0,1,1,0,7,0,2,0,1,0,0,0,0,0,0,1,0,1,0,0,3,0,0,3,2,2,0,0,1,1,1,0,0,0,1,1,1,0,3,1,1,0,1,0,4,2,3,0,2,0,1,1,0,0,1,0,3,1,1,0,2,1,1,0,1,1,0,1,0,0,0,0,3,0,1,1,0,0,3,1,0,8,1,0,3,2,4,0,1,3" [left031Row5Part2]

private noncomputable def left031Row5Part0 : List ℕ := native_gaps% "0,0,0,4,0,1,0,0,0,1,0,4,1,0,0,0,0,0,1,3,2,0,1,1,0,0,0,2,0,4,0,0,0,0,3,2,0,0,0,1,0,1,2,1,0,0,0,2,2,1,0,0,0,0,5,0,5,2,0,0,1,0,3,0,0,1,2,1,0,0,79,0,18,2,0,0,0,0,0,2,3,1,4,0,0,1,0,1,2,1,1,0,1,1,1,0,0,1,0,3,0,1,5,0,0,0,1,2,5,4,1,0,1,4,1,0,2,0,2,1,0,1,1,0,4,3,0,2" [left031Row5Part1]

private noncomputable def left031Row5 : List ℕ := left031Row5Part0

private noncomputable def left031Row6Part5 : List ℕ := native_gaps% "1,0,1,0,0,0,0,1,0,2,3,0,5,3,3,0,2,1,1,1,1,4,1,0,1,0,3,0,0,0,1,0,1,0,0,0,1,1,0,1,0,2,0,0,1,1,0,0,2,6,2" [[]]

private noncomputable def left031Row6Part4 : List ℕ := native_gaps% "0,4,1,0,2,0,0,0,3,1,0,1,0,2,1,3,1,0,1,1,3,1,0,0,0,4,0,1,2,1,2,0,1,0,1,1,0,1,0,1,0,2,2,1,0,0,0,2,0,0,1,0,0,4,4,0,4,0,1,1,2,0,3,0,2,2,2,0,1,2,0,0,0,1,1,0,4,1,0,0,0,0,1,1,0,0,1,0,0,1,0,0,0,0,1,1,2,2,2,1,1,0,3,0,2,0,0,0,1,0,2,0,2,0,1,0,0,0,1,0,3,1,0,3,2,0,0,0" [left031Row6Part5]

private noncomputable def left031Row6Part3 : List ℕ := native_gaps% "1,0,0,0,0,0,6,1,0,0,0,0,2,0,0,1,0,2,1,0,1,5,4,0,2,4,0,2,0,0,1,0,2,2,0,1,1,1,1,1,0,0,2,0,1,1,0,9,1,7,0,1,0,4,0,1,0,0,0,1,2,0,0,2,0,1,1,2,0,0,0,0,1,0,0,1,0,3,1,0,0,0,0,2,1,0,0,0,0,0,2,0,0,1,2,1,1,0,3,0,0,3,1,0,0,2,6,1,0,0,0,2,1,2,1,1,1,1,0,4,5,2,1,0,1,0,0,0" [left031Row6Part4]

private noncomputable def left031Row6Part2 : List ℕ := native_gaps% "1,0,1,0,2,1,2,1,1,1,0,1,0,1,5,1,0,6,0,2,1,0,0,4,0,1,1,6,0,0,0,1,0,1,3,1,0,0,0,1,2,5,1,0,2,0,5,0,0,0,2,2,0,2,1,2,0,0,6,0,0,2,0,0,1,0,0,0,1,1,0,1,2,2,0,0,2,2,1,0,1,0,0,1,2,4,1,0,0,0,0,0,0,6,0,1,0,0,0,0,0,0,2,2,2,0,0,0,2,2,0,1,0,6,1,3,1,0,0,1,0,0,0,3,0,0,0,2" [left031Row6Part3]

private noncomputable def left031Row6Part1 : List ℕ := native_gaps% "0,1,0,0,1,2,0,2,2,0,0,0,3,0,0,2,0,0,2,0,0,1,0,0,0,0,0,0,0,1,2,0,0,0,0,0,1,4,1,1,0,0,0,0,1,1,0,0,0,0,0,1,1,0,3,0,7,0,0,1,0,1,0,2,2,0,1,0,2,0,0,0,0,1,0,0,4,5,1,0,2,0,0,0,2,0,2,0,1,0,2,0,0,0,1,0,2,2,0,0,0,0,0,0,2,0,1,0,3,0,0,2,0,0,5,1,2,2,4,1,0,5,1,0,0,1,0,4" [left031Row6Part2]

private noncomputable def left031Row6Part0 : List ℕ := native_gaps% "0,0,1,1,0,0,0,1,0,1,3,0,0,0,4,0,2,1,0,0,2,0,0,0,1,1,1,1,0,1,0,1,0,1,4,1,0,1,5,0,1,0,0,7,1,0,2,1,7,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,2,0,0,2,77,0,21,2,1,1,2,0,5,2,0,5,0,2,1,1,1,0,0,2,3,3,0,1,5,1,0,1,3,0,3,4,2,2,0,0,3,0,0,3,0,2,0,3,0,0,0,0,2,3,1,5,0,1,0,0,0,0,1" [left031Row6Part1]

private noncomputable def left031Row6 : List ℕ := left031Row6Part0

private noncomputable def left031Row7Part5 : List ℕ := native_gaps% "0,0,2,5,5,0,1,1,0,0,7,0,2,2,2,3,0,0,1,0,0,2,2,2,0,3,0,0,1,0,0,2,1,1,0,0,0,1,0,8,0,2,0,0,0,2,0,0,5,4" [[]]

private noncomputable def left031Row7Part4 : List ℕ := native_gaps% "0,3,2,3,2,1,3,2,0,4,1,0,2,0,0,0,0,0,3,1,0,1,0,1,7,4,3,1,1,3,0,2,2,2,0,0,3,0,1,1,0,0,0,0,1,0,4,1,1,1,0,0,0,0,1,0,0,3,1,2,1,0,3,0,1,0,0,3,0,0,0,1,0,0,0,0,0,0,1,0,0,1,0,0,0,0,0,7,1,0,0,1,2,0,1,0,2,0,2,0,3,1,0,2,1,0,2,5,0,2,1,1,0,1,0,1,2,3,2,1,0,0,0,0,2,4,3,0" [left031Row7Part5]

private noncomputable def left031Row7Part3 : List ℕ := native_gaps% "0,2,3,1,1,1,1,1,3,1,0,1,3,0,1,1,5,0,1,0,0,0,5,0,0,0,4,3,3,0,1,0,0,0,2,0,0,0,2,1,0,0,0,0,0,1,2,1,0,2,0,1,4,0,0,0,0,1,2,2,9,2,0,2,0,0,3,0,1,1,0,1,0,1,0,2,0,4,1,2,0,1,0,2,0,0,2,1,1,1,1,1,1,0,0,2,0,0,0,0,0,1,0,1,2,0,0,1,0,0,2,2,1,0,0,2,1,0,1,0,0,0,1,1,0,1,2,2" [left031Row7Part4]

private noncomputable def left031Row7Part2 : List ℕ := native_gaps% "1,0,0,2,1,0,0,1,0,1,0,0,0,1,1,0,0,1,1,4,2,0,0,2,1,1,1,0,3,2,0,0,0,1,2,0,0,2,7,2,1,0,1,3,0,1,0,2,0,0,2,2,0,0,0,2,0,2,0,0,2,4,0,2,1,1,2,2,4,2,1,0,0,1,0,5,0,1,2,0,2,2,4,0,0,0,0,0,0,4,0,1,2,2,0,0,2,0,0,1,0,0,1,0,4,5,0,1,1,0,3,2,0,0,1,0,0,0,0,3,0,0,0,0,0,0,0,0" [left031Row7Part3]

private noncomputable def left031Row7Part1 : List ℕ := native_gaps% "0,0,1,0,1,1,1,0,1,0,1,0,0,0,4,1,0,2,0,0,0,1,3,1,0,0,0,0,1,0,0,1,0,1,1,1,0,4,0,2,0,0,1,0,0,1,0,1,1,0,0,0,0,1,0,1,0,0,0,0,3,1,0,0,1,2,0,1,3,0,0,1,2,0,0,1,0,0,2,12,2,2,1,0,1,0,10,2,1,0,1,0,0,0,0,0,1,1,1,0,0,0,4,0,2,1,0,0,0,0,0,0,0,0,1,0,0,1,0,0,0,1,0,1,1,0,0,0" [left031Row7Part2]

private noncomputable def left031Row7Part0 : List ℕ := native_gaps% "0,0,1,1,1,0,0,4,1,0,0,0,3,0,1,2,0,0,0,1,1,0,0,2,0,2,2,0,0,0,2,2,0,0,4,3,0,3,1,2,4,0,2,0,3,5,1,0,0,1,0,0,0,3,2,1,2,1,5,2,76,0,0,0,18,0,0,0,1,1,0,0,2,2,0,0,0,1,3,0,1,0,0,0,0,0,0,0,2,1,1,0,0,0,0,1,0,6,0,1,2,3,3,0,1,2,3,0,1,0,3,3,1,4,0,2,0,0,0,1,2,0,0,1,1,2,2,2" [left031Row7Part1]

private noncomputable def left031Row7 : List ℕ := left031Row7Part0

private noncomputable def leftGaps031 : List (List ℕ) := [left031Row0, left031Row1, left031Row2, left031Row3, left031Row4, left031Row5, left031Row6, left031Row7]

private noncomputable def right031Row0Part4 : List ℕ := native_gaps% "2,2,2,0,1,2,1,0,0,0,2,0,0,0,1,0,0,0,3,1,1,0,1,0,1,1,10,0,1,2,3,0,3,0,0,1,0,2,0,4,0,3,0,1,0,2,2,0,0,0,2,0,2,4,1,1,1,0,1,0,0,2,1,0,5,2,0,1,3,0,0,0,2,1,0,1,1,0,0,0,1,2,1,0,0,3,0,0,0,0,0,2,3,0,0,7,0,3,0,0,0,0,1,3,0,4,1,1,0,0,1,0" [[]]

private noncomputable def right031Row0Part3 : List ℕ := native_gaps% "1,2,4,0,4,0,0,0,0,0,4,0,0,1,1,2,0,0,0,2,0,1,0,0,1,2,0,1,0,0,0,4,1,1,0,1,0,0,0,0,7,0,3,0,0,6,2,4,1,1,0,1,2,0,3,0,0,0,4,0,1,0,2,0,0,0,0,1,0,3,0,3,1,2,0,1,1,0,0,2,1,1,0,1,0,0,0,0,5,1,2,1,0,1,2,3,1,0,0,0,0,0,0,0,6,3,0,0,0,2,0,1,0,2,2,0,2,1,2,0,0,0,0,0,1,6,6,0" [right031Row0Part4]

private noncomputable def right031Row0Part2 : List ℕ := native_gaps% "0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,2,1,0,4,0,0,0,0,1,3,1,2,0,2,1,1,0,1,1,1,0,0,4,7,2,0,0,0,3,2,0,0,1,0,10,0,0,2,1,1,1,1,0,2,2,2,0,0,1,0,2,0,0,4,0,1,1,1,2,2,0,0,0,1,1,0,0,0,0,2,2,0,2,0,0,0,0,0,1,2,0,0,2,0,0,2,1,1,4,0,2,0,3,0,1,0,1,0,0,2,0,1,0,0,1,0,0,0,2,0,1,0,1" [right031Row0Part3]

private noncomputable def right031Row0Part1 : List ℕ := native_gaps% "0,2,2,2,1,0,1,1,0,1,0,0,3,0,2,7,0,1,7,1,2,1,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,2,0,4,0,2,1,0,1,0,0,0,1,0,0,0,0,0,2,0,0,6,0,6,1,0,2,2,0,1,0,1,0,1,0,0,1,3,0,1,0,0,0,0,0,1,0,1,2,0,0,2,0,0,3,3,0,2,0,0,1,1,2,0,3,6,0,1,4,2,0,1,0,5,1,2,2,0,0,0,0,1,0,0,3,2,2,0,0,4,0,0" [right031Row0Part2]

private noncomputable def right031Row0Part0 : List ℕ := native_gaps% "0,3,2,0,0,0,0,1,0,1,1,0,0,0,0,0,2,0,0,1,3,1,0,0,0,1,0,0,0,0,0,0,0,1,2,0,0,2,0,3,8,1,3,0,2,2,2,1,0,2,0,0,0,0,3,1,4,0,0,0,3,0,3,0,1,0,2,1,3,0,0,1,0,0,5,2,4,1,2,1,1,0,0,0,0,0,0,0,2,2,0,0,1,0,0,1,0,1,0,1,1,1,2,1,2,0,0,2,2,1,0,0,0,2,2,0,0,4,0,0,0,0,1,1,0,1,2,0" [right031Row0Part1]

private noncomputable def right031Row0 : List ℕ := right031Row0Part0

private noncomputable def right031Row1Part4 : List ℕ := native_gaps% "2,1,0,0,1,2,1,2,0,1,0,1,2,0,2,0,2,0,1,2,0,0,3,0,3,1,2,1,1,0,0,1,0,3,0,2,1,2,3,0,2,3,0,1,4,1,2,1,0,3,0,2,2,3,0,0,0,0,0,0,2,0,0,0,1,0,2,0,1,0,0,5,1,0,1,1,4,1,0,2,0,0,3,0,0,0,0,1,3,1,1,0,1" [[]]

private noncomputable def right031Row1Part3 : List ℕ := native_gaps% "0,2,0,1,0,1,0,0,3,1,0,4,1,5,0,0,4,0,2,0,0,0,3,0,6,2,2,0,2,0,1,0,2,2,0,0,0,0,0,0,2,0,2,1,2,2,2,2,0,0,1,2,2,0,2,4,3,1,0,0,1,3,0,0,2,2,0,1,0,0,2,1,0,1,0,0,0,2,0,0,0,2,1,0,0,0,1,1,3,2,2,0,0,0,1,0,2,0,0,3,0,1,1,0,0,1,2,0,1,0,0,1,0,0,2,4,1,3,0,1,2,2,5,0,3,1,1,2" [right031Row1Part4]

private noncomputable def right031Row1Part2 : List ℕ := native_gaps% "1,1,0,0,1,1,0,0,4,1,2,0,0,1,2,0,1,3,0,1,3,1,0,0,3,5,0,0,0,1,0,0,2,1,4,3,0,1,0,0,0,3,5,1,0,3,4,0,1,1,2,2,2,0,1,1,4,0,0,2,8,2,1,2,3,1,1,4,0,0,0,2,0,0,0,2,4,3,0,0,1,1,3,1,0,1,2,1,5,0,2,0,0,1,0,0,0,0,3,1,2,4,2,0,0,0,2,1,0,0,2,3,0,1,1,1,1,0,1,0,0,1,0,0,0,1,0,1" [right031Row1Part3]

private noncomputable def right031Row1Part1 : List ℕ := native_gaps% "0,1,1,1,0,1,0,1,2,0,0,0,1,0,1,0,2,1,2,3,1,0,0,2,2,0,0,0,2,1,0,0,0,0,0,2,0,0,0,4,0,1,2,0,0,0,1,0,0,2,0,1,2,0,0,0,4,1,0,0,0,1,0,2,0,0,0,0,0,0,0,0,0,2,2,1,0,0,0,1,0,1,0,0,1,0,0,0,1,2,0,3,0,2,0,2,3,0,0,0,0,1,1,1,0,0,1,0,0,0,0,4,1,0,0,0,0,0,3,0,0,0,2,0,2,1,0,4" [right031Row1Part2]

private noncomputable def right031Row1Part0 : List ℕ := native_gaps% "1,0,1,0,1,2,6,0,0,0,0,0,1,1,3,0,0,5,1,3,0,0,0,0,0,1,5,11,0,0,0,1,1,1,0,1,1,1,0,1,2,2,2,0,0,2,2,1,1,1,1,1,0,2,0,4,1,7,0,3,1,1,0,0,1,4,1,0,3,0,1,0,0,0,1,2,0,1,0,5,0,0,0,0,2,0,2,0,3,0,2,5,1,0,1,0,1,0,2,1,2,0,0,4,1,3,1,0,1,4,0,0,0,2,0,1,0,0,0,0,0,2,0,3,2,0,3,1" [right031Row1Part1]

private noncomputable def right031Row1 : List ℕ := right031Row1Part0

private noncomputable def right031Row2Part4 : List ℕ := native_gaps% "0,0,0,1,0,2,3,1,0,1,1,1,2,0,0,0,1,0,0,0,0,0,2,0,3,3,0,2,1,0,0,4,0,1,2,1,0,0,1,1,0,1,0,0,3,0,0,3,3,1,0,2,2,3,0,2,4,0,0,0,1,0,1,0,0,0,1,0,0,0,3,0,2,1,2,0,1,1,0,0,0,2,0,2,0,0,2,0,3,0,0,0,0,0,3,2,1,0" [[]]

private noncomputable def right031Row2Part3 : List ℕ := native_gaps% "2,1,1,1,3,0,3,1,2,1,0,1,0,0,1,1,0,0,2,0,0,0,1,3,0,1,1,0,2,1,4,1,0,2,0,0,2,0,0,0,3,3,3,1,1,2,0,0,0,1,0,0,0,0,1,2,1,0,0,2,0,1,0,0,0,1,0,0,3,0,0,0,0,1,2,1,0,1,2,0,1,2,2,0,1,1,0,1,1,0,3,0,0,0,0,4,0,0,2,3,0,1,2,2,0,1,1,0,1,0,0,0,3,0,0,0,0,0,0,1,0,4,3,3,1,0,0,0" [right031Row2Part4]

private noncomputable def right031Row2Part2 : List ℕ := native_gaps% "2,0,0,0,4,0,3,2,0,1,0,1,0,3,0,1,3,3,0,0,0,0,4,1,1,1,0,1,0,2,0,2,3,1,1,2,0,0,3,1,0,0,1,0,0,3,1,1,3,7,0,1,0,1,9,2,0,0,0,0,0,0,1,0,0,5,2,1,0,0,0,3,1,0,0,1,0,1,0,4,1,0,0,0,1,0,0,0,2,0,1,0,2,4,0,1,0,2,2,2,2,0,0,0,2,0,0,2,0,1,0,3,0,0,0,0,5,2,0,0,1,5,3,0,3,0,0,0" [right031Row2Part3]

private noncomputable def right031Row2Part1 : List ℕ := native_gaps% "0,1,0,1,3,0,0,1,1,0,5,5,0,2,1,0,0,2,2,1,0,0,0,0,0,1,3,2,0,0,0,0,0,1,0,3,1,1,1,2,2,1,1,0,0,1,0,1,2,2,1,1,2,2,0,1,4,0,2,0,0,4,1,0,0,1,0,1,1,0,0,1,1,0,0,1,3,0,2,0,1,1,5,1,1,1,0,0,5,1,0,7,0,2,0,1,2,3,1,3,0,1,1,0,2,1,0,1,1,0,0,0,0,2,1,0,2,0,0,1,0,3,4,2,1,1,3,3" [right031Row2Part2]

private noncomputable def right031Row2Part0 : List ℕ := native_gaps% "2,1,0,2,1,1,2,5,1,1,0,0,2,0,0,4,0,2,0,0,4,0,2,1,0,0,0,1,0,0,0,1,0,0,0,1,7,1,0,1,2,1,0,0,0,0,2,0,0,1,1,2,3,0,6,2,0,0,3,7,2,5,0,1,0,0,0,0,1,2,0,0,0,4,0,0,2,6,9,0,0,1,0,0,1,0,0,0,1,0,0,0,0,0,0,2,1,1,0,3,1,0,0,3,2,0,0,1,3,0,0,0,4,1,1,0,5,0,0,0,1,1,2,0,4,1,0,1" [right031Row2Part1]

private noncomputable def right031Row2 : List ℕ := right031Row2Part0

private noncomputable def right031Row3Part4 : List ℕ := native_gaps% "3,0,0,0,0,1,0,0,1,0,4,1,2,0,8,0,0,3,3,0,0,2,3,0,1,0,0,0,0,0,0,2,0,1,0,0,0,0,0,1,1,2,0,2,2,0,0,0,2,0,1,1,1,0,0,0,0,1,0,1,0,0,0,1,0,0,10,3,1,3,2,0,0,0,0,1,0,2,0,1,1,0,0,0,1,0,0,1,3,0,0,0,0,0,2,0,1,3,0,0,0,1,0,0,3,3,5,1,2,0,1,0,0,1,1,1,1,0,0,3,3,0,2,0,0" [[]]

private noncomputable def right031Row3Part3 : List ℕ := native_gaps% "0,2,0,0,0,0,0,2,0,0,0,0,1,6,4,0,0,2,0,2,5,3,13,0,1,1,1,1,2,6,0,0,0,0,0,0,3,3,0,0,1,0,0,0,1,0,0,8,0,2,1,0,0,5,0,0,1,2,0,0,1,1,1,0,0,3,2,0,1,0,0,0,0,0,0,0,0,4,1,2,0,0,1,1,0,0,3,0,1,1,0,1,0,1,1,0,0,1,0,2,0,1,1,0,2,3,1,1,1,0,2,0,0,2,0,0,0,0,0,2,1,6,1,2,0,0,0,1" [right031Row3Part4]

private noncomputable def right031Row3Part2 : List ℕ := native_gaps% "1,0,2,0,0,4,2,0,2,0,1,0,0,7,1,0,3,0,4,1,5,1,1,1,1,0,1,1,0,2,0,0,0,1,1,0,2,0,1,0,2,0,1,0,0,0,0,0,0,1,1,0,0,4,0,0,1,0,2,0,1,0,0,1,1,4,1,0,0,1,1,2,0,3,0,0,2,0,7,0,1,0,0,0,0,2,5,0,3,0,0,0,1,0,0,3,1,0,0,1,1,3,0,2,0,0,2,0,0,2,0,1,1,3,0,2,0,1,1,0,0,0,1,0,3,1,0,1" [right031Row3Part3]

private noncomputable def right031Row3Part1 : List ℕ := native_gaps% "0,0,1,1,0,1,1,2,3,0,0,0,0,0,2,2,6,0,0,0,0,1,0,3,0,1,0,4,1,2,1,0,0,0,1,2,2,0,0,0,0,0,1,1,0,1,1,1,4,0,2,0,0,1,0,1,1,2,0,0,2,0,0,0,1,0,0,2,0,0,1,6,2,0,1,2,1,2,0,3,0,0,2,1,1,0,2,1,0,0,0,1,2,0,0,0,0,0,0,1,0,2,0,3,0,2,0,1,1,3,2,1,0,0,0,0,3,0,1,3,0,0,0,0,2,0,5,0" [right031Row3Part2]

private noncomputable def right031Row3Part0 : List ℕ := native_gaps% "1,1,2,1,0,0,1,0,0,0,2,1,0,1,1,0,0,1,0,1,1,0,0,3,0,1,4,0,0,0,0,1,1,5,2,0,2,3,2,1,1,0,1,1,1,0,0,2,2,4,0,0,2,0,3,1,5,1,0,0,0,0,1,2,1,2,0,0,0,0,0,0,0,1,1,0,1,1,0,0,0,0,0,0,1,0,0,3,0,1,1,0,0,0,2,0,1,0,2,1,5,3,0,2,1,0,1,1,0,0,0,0,7,0,1,3,1,0,0,0,0,1,0,1,3,0,0,1" [right031Row3Part1]

private noncomputable def right031Row3 : List ℕ := right031Row3Part0

private noncomputable def right031Row4Part5 : List ℕ := native_gaps% "0,1,1,1,1,1,4,2,1" [[]]

private noncomputable def right031Row4Part4 : List ℕ := native_gaps% "3,1,0,3,2,2,1,0,7,0,1,0,0,0,2,4,0,2,0,0,0,2,1,0,1,0,0,0,1,0,2,0,1,0,1,1,2,0,0,2,0,0,2,0,0,1,0,0,5,1,0,0,0,0,1,0,1,0,0,0,0,0,2,2,1,1,0,2,1,0,1,1,3,0,0,1,0,0,1,1,1,0,4,1,1,0,2,1,0,0,0,0,0,2,3,2,3,0,0,2,0,0,1,2,2,0,1,1,1,1,1,0,1,0,1,1,0,2,0,2,0,0,1,0,1,2,0,1" [right031Row4Part5]

private noncomputable def right031Row4Part3 : List ℕ := native_gaps% "0,1,0,1,2,1,3,4,2,3,0,0,3,1,0,1,0,1,1,1,1,1,0,0,0,2,1,3,1,0,1,0,0,0,1,1,0,4,0,2,0,0,1,0,1,1,0,0,0,1,0,1,0,0,0,1,2,0,1,3,4,3,0,0,0,0,1,0,0,2,2,0,4,3,1,1,0,1,0,2,1,0,0,0,1,1,1,2,6,1,0,0,0,2,0,1,0,1,0,0,0,0,0,0,0,0,1,1,1,0,0,0,1,0,0,0,0,0,4,0,0,1,0,0,0,1,0,0" [right031Row4Part4]

private noncomputable def right031Row4Part2 : List ℕ := native_gaps% "3,2,1,0,1,3,0,1,0,2,0,0,1,0,0,0,0,1,0,1,0,0,2,2,0,0,1,0,6,0,1,0,0,1,1,1,1,0,1,0,2,1,0,3,2,1,0,1,1,0,2,0,0,0,0,5,2,0,0,0,0,0,0,3,1,2,2,0,0,1,0,2,1,1,2,2,0,9,3,2,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,3,1,0,1,1,0,2,0,1,3,2,3,3,2,0,0,2,0,0,3,0,0,0,2,0,0,2,0,1,2,0,0,0" [right031Row4Part3]

private noncomputable def right031Row4Part1 : List ℕ := native_gaps% "0,1,1,0,0,0,1,0,0,0,0,0,4,1,0,0,0,1,1,1,0,0,1,3,2,0,2,2,2,3,0,0,1,0,2,1,0,0,2,0,0,2,0,0,2,0,3,0,0,1,0,0,3,0,0,1,0,0,0,2,1,0,0,2,1,1,0,2,0,1,1,0,6,3,2,0,0,0,0,1,1,0,1,0,0,1,1,1,1,5,5,0,1,2,1,0,1,2,2,2,0,0,1,1,0,2,1,0,0,3,0,2,1,1,2,0,2,0,4,0,2,4,0,0,0,2,2,0" [right031Row4Part2]

private noncomputable def right031Row4Part0 : List ℕ := native_gaps% "0,4,4,0,0,1,0,1,0,2,1,1,0,0,1,1,0,1,0,0,0,0,0,0,0,0,2,0,0,1,0,2,0,1,3,1,1,0,2,0,0,0,4,0,1,0,3,0,1,2,2,0,0,3,1,0,0,1,1,1,0,1,4,1,1,1,0,1,0,2,4,3,0,0,0,2,1,2,0,2,2,3,0,0,0,0,0,0,4,2,1,0,0,0,0,4,0,0,0,1,0,4,0,2,2,1,2,0,0,0,0,0,0,0,1,1,5,1,0,1,0,0,0,2,0,0,0,0" [right031Row4Part1]

private noncomputable def right031Row4 : List ℕ := right031Row4Part0

private noncomputable def right031Row5Part4 : List ℕ := native_gaps% "6,0,0,0,1,1,1,3,0,1,2,0,1,0,0,0,0,1,1,2,0,1,3,0,1,5,1,2,1,0,1,2,0,1,3,2,0,0,0,4,0,0,1,0,1,0,1,0,0,0,0,1,0,2,2,2,1,3,1,3,0,0,1,3,0,0,1,0,1,2,0,3,2,1,1,0,0,0,0,0,1,0,3,3,0,0,0,0,1,0,3,0,1,2,1,0,1,1,0,1,0,0,0,1,1,2,0,6,0" [[]]

private noncomputable def right031Row5Part3 : List ℕ := native_gaps% "0,0,1,2,0,0,0,1,2,0,0,2,0,1,2,1,0,1,0,2,0,1,4,0,0,3,1,1,1,0,0,0,0,1,1,0,0,0,1,2,1,2,0,0,0,1,0,0,0,2,0,0,1,3,0,5,0,3,1,1,0,2,2,0,1,0,1,1,1,0,0,2,0,1,2,1,0,0,2,1,3,3,0,2,2,0,0,1,0,1,0,1,0,2,0,2,1,0,2,0,1,0,2,5,0,0,0,1,1,1,0,1,2,0,0,4,0,2,2,0,0,0,2,0,1,1,2,2" [right031Row5Part4]

private noncomputable def right031Row5Part2 : List ℕ := native_gaps% "2,1,1,0,1,0,0,1,0,2,1,0,0,0,2,0,0,0,0,1,0,0,0,0,0,0,0,2,0,0,0,1,0,0,1,0,0,1,1,1,4,0,0,0,0,2,0,2,0,2,0,0,0,0,0,2,0,1,5,0,0,1,1,1,2,1,0,0,0,0,1,0,1,0,3,1,0,0,4,0,1,0,0,1,0,0,2,0,1,0,0,0,0,0,2,1,0,0,0,0,0,3,3,0,1,0,0,1,1,4,2,5,0,1,1,2,1,0,1,0,1,1,2,0,5,1,2,0" [right031Row5Part3]

private noncomputable def right031Row5Part1 : List ℕ := native_gaps% "1,4,2,0,0,1,1,0,7,0,1,0,1,0,1,1,0,1,1,2,1,0,0,2,2,0,0,2,4,1,1,0,0,1,3,4,1,0,0,0,1,3,1,0,1,3,0,1,1,1,0,0,3,0,0,0,3,1,0,5,14,1,1,2,0,2,0,0,4,2,0,1,0,4,1,4,1,0,0,4,0,3,2,1,2,0,0,0,0,0,0,1,0,0,1,0,0,3,0,1,1,2,0,0,0,0,0,0,4,0,2,0,1,3,0,3,1,0,0,2,2,0,3,3,0,2,0,0" [right031Row5Part2]

private noncomputable def right031Row5Part0 : List ℕ := native_gaps% "0,6,4,6,0,0,3,1,0,0,0,0,0,0,2,1,2,0,0,3,1,2,0,0,4,1,0,0,0,3,1,1,0,3,2,0,0,0,0,2,0,1,1,2,2,1,4,1,0,0,3,0,4,0,2,1,0,7,0,0,0,0,0,1,0,2,2,0,0,4,1,1,2,0,0,1,0,2,1,0,0,2,2,0,0,2,1,0,4,1,0,0,0,2,1,1,0,4,0,0,0,1,1,0,0,0,3,5,3,0,1,1,0,0,2,0,1,0,1,3,0,3,2,1,0,0,0,0" [right031Row5Part1]

private noncomputable def right031Row5 : List ℕ := right031Row5Part0

private noncomputable def right031Row6Part4 : List ℕ := native_gaps% "0,1,1,0,6,0,1,0,0,0,3,1,0,1,2,0,0,0,1,0,1,2,0,0,0,0,0,0,3,2,0,0,0,0,0,2,2,0,0,0,0,0,0,4,5,0,0,0,2,0,1,0,4,3,2,0,3,0,0,0,0,1,0,1,0,1,0,0,1,0,0,0,0,2,0,0,0,0,0,0,5,0" [[]]

private noncomputable def right031Row6Part3 : List ℕ := native_gaps% "0,1,0,1,1,1,6,0,0,0,0,2,0,4,2,0,0,0,6,2,1,0,0,0,1,2,3,5,2,1,1,1,1,0,2,1,0,0,0,3,1,3,1,0,0,0,0,4,1,0,0,1,8,0,2,3,1,0,0,1,0,2,0,0,0,1,1,1,0,0,1,2,1,1,0,0,0,1,0,4,5,1,5,0,0,1,7,1,0,1,0,1,0,1,0,0,0,0,0,0,3,0,0,2,0,0,1,0,1,0,2,0,0,0,2,4,0,2,0,0,1,0,2,1,2,1,0,0" [right031Row6Part4]

private noncomputable def right031Row6Part2 : List ℕ := native_gaps% "0,3,0,2,2,1,0,3,1,1,1,2,1,4,2,0,0,0,0,0,0,1,1,0,0,5,2,0,1,7,1,0,4,4,0,2,6,4,1,0,0,2,0,1,2,4,5,0,1,3,0,0,0,3,2,1,0,0,0,0,0,0,2,1,3,0,3,1,0,2,0,0,0,2,0,0,3,0,0,1,4,3,0,0,2,1,0,0,0,1,0,0,0,3,0,2,1,2,3,1,0,0,1,1,6,0,0,5,1,0,0,0,2,0,2,1,2,3,0,2,0,1,2,0,1,3,0,1" [right031Row6Part3]

private noncomputable def right031Row6Part1 : List ℕ := native_gaps% "1,1,0,1,0,1,1,0,0,2,6,2,7,0,5,0,1,1,0,1,2,0,0,2,1,0,0,0,1,2,0,2,0,2,3,0,0,0,1,5,0,2,0,0,1,2,1,3,2,1,1,2,1,0,0,0,2,2,0,0,0,0,2,2,0,2,1,2,1,1,0,0,0,0,3,3,1,2,0,0,0,1,2,1,2,0,0,0,0,0,0,1,0,0,3,1,4,1,1,2,0,0,1,5,0,0,0,3,0,0,5,0,2,0,1,1,1,3,0,7,1,1,3,1,0,0,3,3" [right031Row6Part2]

private noncomputable def right031Row6Part0 : List ℕ := native_gaps% "3,0,1,2,3,0,0,0,1,0,1,0,5,1,1,0,0,2,2,0,1,1,0,0,1,1,0,0,0,1,0,0,2,0,1,2,1,0,0,1,2,0,0,0,3,0,2,0,4,0,0,1,2,0,0,0,1,0,2,1,7,0,0,1,5,0,0,0,2,1,0,0,1,0,2,0,1,8,0,1,0,2,1,0,5,0,5,0,0,0,1,1,0,3,5,2,0,0,1,0,0,5,2,2,0,0,1,2,1,0,0,1,1,1,0,0,1,0,1,0,0,2,1,2,1,2,0,1" [right031Row6Part1]

private noncomputable def right031Row6 : List ℕ := right031Row6Part0

private noncomputable def right031Row7Part4 : List ℕ := native_gaps% "4,1,0,0,0,1,0,0,0,3,0,0,0,4,0,1,0,1,1,0,4,1,0,0,0,1,0,2,2,2,0,0,0,0,0,4,0,0,0,2,0,1,0,0,4,1,0,0,1,3,0,3,0,0,1,5,0,0,1,1,1,0,0,1,0,1,2,0,0,1,3,1,0,1,1,0,0,0,0,0,2,0,1,0,0,0,0,0,0,0,0,0,0,2,1,0,5,4,0,0,0,0,0,0,0,0,1,0,0,0,1,5,2,0,0,1,2" [[]]

private noncomputable def right031Row7Part3 : List ℕ := native_gaps% "1,1,1,1,0,1,0,0,1,2,1,1,0,0,0,0,0,1,0,0,0,2,1,2,0,6,0,0,0,1,0,0,0,0,0,4,1,0,1,3,0,0,4,0,1,3,1,2,0,0,0,1,0,0,3,0,2,2,3,0,2,0,0,0,0,2,0,1,0,1,0,4,0,1,1,1,2,1,0,0,0,2,0,0,1,0,10,5,4,0,1,8,0,1,0,0,1,0,0,5,3,1,2,1,0,0,0,0,3,0,1,3,0,1,0,1,3,2,0,1,3,0,2,0,1,0,0,2" [right031Row7Part4]

private noncomputable def right031Row7Part2 : List ℕ := native_gaps% "3,0,2,0,3,1,0,0,1,0,0,0,3,1,2,1,0,2,0,0,3,0,1,2,4,0,1,1,0,2,0,3,0,0,0,0,0,2,1,1,2,2,1,2,2,0,0,0,1,0,0,0,0,1,1,1,1,7,0,1,1,0,3,0,1,1,0,4,0,0,1,1,1,2,0,0,2,0,3,1,0,3,3,0,2,1,2,2,6,0,1,1,1,2,0,6,0,3,0,0,1,0,0,2,3,1,6,1,0,2,1,1,1,1,0,0,0,1,0,0,0,0,1,1,0,3,0,0" [right031Row7Part3]

private noncomputable def right031Row7Part1 : List ℕ := native_gaps% "0,0,0,2,0,3,0,1,0,1,1,0,0,1,1,8,0,3,4,0,1,0,5,0,1,0,0,0,0,3,1,0,0,0,0,3,1,0,0,4,0,1,0,1,1,1,2,0,0,4,0,0,2,2,0,1,0,3,0,2,1,0,1,2,0,1,3,0,0,0,0,0,0,0,0,2,0,3,0,2,3,0,2,1,0,0,1,1,1,0,0,4,0,5,0,2,0,1,1,0,0,0,2,6,0,0,0,1,0,1,0,0,4,0,0,0,0,0,0,0,3,0,0,0,2,1,1,0" [right031Row7Part2]

private noncomputable def right031Row7Part0 : List ℕ := native_gaps% "2,1,1,2,0,1,0,3,0,1,0,0,0,0,5,0,1,0,0,1,0,0,1,0,0,1,0,0,2,1,0,0,0,1,1,4,2,0,2,0,1,1,1,1,2,0,2,0,0,0,1,0,1,0,0,0,0,2,0,0,0,4,0,0,0,1,1,0,5,1,0,0,0,4,0,6,0,1,1,0,0,1,0,2,4,4,0,0,0,3,0,1,0,8,1,1,1,2,1,0,1,1,0,0,0,3,0,0,0,0,3,1,0,1,1,1,1,0,1,2,0,0,0,0,2,0,0,0" [right031Row7Part1]

private noncomputable def right031Row7 : List ℕ := right031Row7Part0

private noncomputable def rightGaps031 : List (List ℕ) := [right031Row0, right031Row1, right031Row2, right031Row3, right031Row4, right031Row5, right031Row6, right031Row7]

private theorem leftMask031 :
    (leftGaps031.map gapMask == (sourceTransposeA.drop 248).take 8) = true := by
  decide +kernel

private theorem rightMask031 :
    (rightGaps031.map gapMask == (quotientTransposeRows.drop 248).take 8) = true := by
  decide +kernel

private theorem products031 :
    (leftGaps031.map (gapRow quotientTransposeRows) == rightGaps031.map (gapRow targetA)) = true := by
  decide +kernel

theorem block031 :
    checkEqualProducts quotientTransposeRows targetA
      ((sourceTransposeA.drop 248).take 8) ((quotientTransposeRows.drop 248).take 8) = true :=
  checkEqualProducts_of_gap_maps _ _ _ _ _ _
    (beq_iff_eq.mp leftMask031) (beq_iff_eq.mp rightMask031)
    (beq_iff_eq.mp products031)

end QuotientGeneratorAChecks
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Subquotient1242
