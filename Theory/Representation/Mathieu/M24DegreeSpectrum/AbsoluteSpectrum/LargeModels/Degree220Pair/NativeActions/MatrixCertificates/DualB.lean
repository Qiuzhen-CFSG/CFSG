module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.Transposes
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.BSquare

/-!
# Checked DualB matrix identity

Packed row checks are reduced by the Lean kernel and interpreted using the
rectangular soundness theorems in `Packed`. All matrices retain the literal
column conventions of the quotient witnesses and the transposed ATLAS data.
Source: James, J. Algebra 27 (1973), 57--111; GM02 Proposition 5.1.
Witness provenance and ATLAS attribution: `source/README.md` and the parent
`NativeActions/source/README.md` and `Degree220Pair/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.CertificateChecks
open CertificatePacked Thompson.BinaryMatrix

-- Keep the bounded kernel reductions sequential within this module.
set_option Elab.async false

set_option maxRecDepth 2048 in
private theorem dual_B_batch00 :
    checkEqualProducts (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop 0).take 20) (((secondB).drop 0).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_B_batch01 :
    checkEqualProducts (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop 20).take 20) (((secondB).drop 20).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_B_batch02 :
    checkEqualProducts (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop 40).take 20) (((secondB).drop 40).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_B_batch03 :
    checkEqualProducts (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop 60).take 20) (((secondB).drop 60).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_B_batch04 :
    checkEqualProducts (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop 80).take 20) (((secondB).drop 80).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_B_batch05 :
    checkEqualProducts (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop 100).take 20) (((secondB).drop 100).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_B_batch06 :
    checkEqualProducts (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop 120).take 20) (((secondB).drop 120).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_B_batch07 :
    checkEqualProducts (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop 140).take 20) (((secondB).drop 140).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_B_batch08 :
    checkEqualProducts (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop 160).take 20) (((secondB).drop 160).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_B_batch09 :
    checkEqualProducts (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop 180).take 20) (((secondB).drop 180).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_B_batch10 :
    checkEqualProducts (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop 200).take 20) (((secondB).drop 200).take 20) = true := by
  decide +kernel

private theorem dual_B_rows : ∀ i : Fin 220,
    combine (firstBSquare) (dualChangeRows.toList)[i.val]! = combine (dualChangeRows.toList) (secondB)[i.val]! := by
  apply forall_batches (blocks := 11) (size := 20) (by decide)
    (fun i => combine (firstBSquare) (dualChangeRows.toList)[i]! = combine (dualChangeRows.toList) (secondB)[i]!)
  intro b j
  have h : checkEqualProducts (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop (b.val * 20)).take 20) (((secondB).drop (b.val * 20)).take 20) = true := by
    fin_cases b
    · exact dual_B_batch00
    · exact dual_B_batch01
    · exact dual_B_batch02
    · exact dual_B_batch03
    · exact dual_B_batch04
    · exact dual_B_batch05
    · exact dual_B_batch06
    · exact dual_B_batch07
    · exact dual_B_batch08
    · exact dual_B_batch09
    · exact dual_B_batch10
  have he := checkEqualProducts_sound (firstBSquare) (dualChangeRows.toList) (((dualChangeRows.toList).drop (b.val * 20)).take 20) (((secondB).drop (b.val * 20)).take 20) h j.val
  simpa only [chunk_entry _ _ _ _ j.isLt] using he

theorem dual_B : dualChange * (matrixB false ^ 2).transpose = matrixB true * dualChange := by
  have h := matrix_equal_products_of_rows (m := 220) (n := 220) (p := 220) (q := 220)
    dualChangeRows.toList firstBSquare secondB dualChangeRows.toList
    (by decide +kernel) (by decide +kernel) dual_B_rows
  rw [secondB_matrix, firstBSquare_matrix] at h
  simp only [matrix_array] at h
  exact h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.CertificateChecks
