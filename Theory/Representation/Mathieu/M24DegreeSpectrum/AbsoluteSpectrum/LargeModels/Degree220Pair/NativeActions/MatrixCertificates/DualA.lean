module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.Transposes

/-!
# Checked DualA matrix identity

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
private theorem dual_A_batch00 :
    checkEqualProducts (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop 0).take 20) (((secondA).drop 0).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_A_batch01 :
    checkEqualProducts (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop 20).take 20) (((secondA).drop 20).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_A_batch02 :
    checkEqualProducts (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop 40).take 20) (((secondA).drop 40).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_A_batch03 :
    checkEqualProducts (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop 60).take 20) (((secondA).drop 60).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_A_batch04 :
    checkEqualProducts (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop 80).take 20) (((secondA).drop 80).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_A_batch05 :
    checkEqualProducts (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop 100).take 20) (((secondA).drop 100).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_A_batch06 :
    checkEqualProducts (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop 120).take 20) (((secondA).drop 120).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_A_batch07 :
    checkEqualProducts (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop 140).take 20) (((secondA).drop 140).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_A_batch08 :
    checkEqualProducts (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop 160).take 20) (((secondA).drop 160).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_A_batch09 :
    checkEqualProducts (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop 180).take 20) (((secondA).drop 180).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_A_batch10 :
    checkEqualProducts (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop 200).take 20) (((secondA).drop 200).take 20) = true := by
  decide +kernel

private theorem dual_A_rows : ∀ i : Fin 220,
    combine (firstRowsA.toList) (dualChangeRows.toList)[i.val]! = combine (dualChangeRows.toList) (secondA)[i.val]! := by
  apply forall_batches (blocks := 11) (size := 20) (by decide)
    (fun i => combine (firstRowsA.toList) (dualChangeRows.toList)[i]! = combine (dualChangeRows.toList) (secondA)[i]!)
  intro b j
  have h : checkEqualProducts (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop (b.val * 20)).take 20) (((secondA).drop (b.val * 20)).take 20) = true := by
    fin_cases b
    · exact dual_A_batch00
    · exact dual_A_batch01
    · exact dual_A_batch02
    · exact dual_A_batch03
    · exact dual_A_batch04
    · exact dual_A_batch05
    · exact dual_A_batch06
    · exact dual_A_batch07
    · exact dual_A_batch08
    · exact dual_A_batch09
    · exact dual_A_batch10
  have he := checkEqualProducts_sound (firstRowsA.toList) (dualChangeRows.toList) (((dualChangeRows.toList).drop (b.val * 20)).take 20) (((secondA).drop (b.val * 20)).take 20) h j.val
  simpa only [chunk_entry _ _ _ _ j.isLt] using he

theorem dual_A : dualChange * (matrixA false).transpose = matrixA true * dualChange := by
  have h := matrix_equal_products_of_rows (m := 220) (n := 220) (p := 220) (q := 220)
    dualChangeRows.toList firstRowsA.toList secondA dualChangeRows.toList
    (by decide +kernel) (by decide +kernel) dual_A_rows
  rw [secondA_matrix] at h
  simp only [matrix_array] at h
  exact h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.CertificateChecks
