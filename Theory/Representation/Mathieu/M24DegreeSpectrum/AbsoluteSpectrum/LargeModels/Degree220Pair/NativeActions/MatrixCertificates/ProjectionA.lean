module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.Transposes

/-!
# Checked ProjectionA matrix identity

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
private theorem projection_A_batch00 :
    checkEqualProducts (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop 0).take 20) (((firstA).drop 0).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_A_batch01 :
    checkEqualProducts (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop 20).take 20) (((firstA).drop 20).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_A_batch02 :
    checkEqualProducts (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop 40).take 20) (((firstA).drop 40).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_A_batch03 :
    checkEqualProducts (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop 60).take 20) (((firstA).drop 60).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_A_batch04 :
    checkEqualProducts (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop 80).take 20) (((firstA).drop 80).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_A_batch05 :
    checkEqualProducts (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop 100).take 20) (((firstA).drop 100).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_A_batch06 :
    checkEqualProducts (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop 120).take 20) (((firstA).drop 120).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_A_batch07 :
    checkEqualProducts (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop 140).take 20) (((firstA).drop 140).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_A_batch08 :
    checkEqualProducts (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop 160).take 20) (((firstA).drop 160).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_A_batch09 :
    checkEqualProducts (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop 180).take 20) (((firstA).drop 180).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_A_batch10 :
    checkEqualProducts (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop 200).take 20) (((firstA).drop 200).take 20) = true := by
  decide +kernel

private theorem projection_A_rows : ∀ i : Fin 220,
    combine (exteriorRowsA.toList) (projectionRows.toList)[i.val]! = combine (projectionRows.toList) (firstA)[i.val]! := by
  apply forall_batches (blocks := 11) (size := 20) (by decide)
    (fun i => combine (exteriorRowsA.toList) (projectionRows.toList)[i]! = combine (projectionRows.toList) (firstA)[i]!)
  intro b j
  have h : checkEqualProducts (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop (b.val * 20)).take 20) (((firstA).drop (b.val * 20)).take 20) = true := by
    fin_cases b
    · exact projection_A_batch00
    · exact projection_A_batch01
    · exact projection_A_batch02
    · exact projection_A_batch03
    · exact projection_A_batch04
    · exact projection_A_batch05
    · exact projection_A_batch06
    · exact projection_A_batch07
    · exact projection_A_batch08
    · exact projection_A_batch09
    · exact projection_A_batch10
  have he := checkEqualProducts_sound (exteriorRowsA.toList) (projectionRows.toList) (((projectionRows.toList).drop (b.val * 20)).take 20) (((firstA).drop (b.val * 20)).take 20) h j.val
  simpa only [chunk_entry _ _ _ _ j.isLt] using he

theorem projection_A : projection * exteriorMatrix false = matrixA false * projection := by
  have h := matrix_equal_products_of_rows (m := 220) (n := 462) (p := 462) (q := 220)
    projectionRows.toList exteriorRowsA.toList firstA projectionRows.toList
    (by decide +kernel) (by decide +kernel) projection_A_rows
  rw [firstA_matrix] at h
  simp only [matrix_array] at h
  exact h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.CertificateChecks
