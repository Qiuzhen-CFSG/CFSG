module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.Rows

/-!
# Checked BSquare matrix identity

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
private theorem firstB_square_batch00 :
    checkProduct (firstRowsB.toList) (((firstRowsB.toList).drop 0).take 20) (((firstBSquare).drop 0).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_square_batch01 :
    checkProduct (firstRowsB.toList) (((firstRowsB.toList).drop 20).take 20) (((firstBSquare).drop 20).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_square_batch02 :
    checkProduct (firstRowsB.toList) (((firstRowsB.toList).drop 40).take 20) (((firstBSquare).drop 40).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_square_batch03 :
    checkProduct (firstRowsB.toList) (((firstRowsB.toList).drop 60).take 20) (((firstBSquare).drop 60).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_square_batch04 :
    checkProduct (firstRowsB.toList) (((firstRowsB.toList).drop 80).take 20) (((firstBSquare).drop 80).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_square_batch05 :
    checkProduct (firstRowsB.toList) (((firstRowsB.toList).drop 100).take 20) (((firstBSquare).drop 100).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_square_batch06 :
    checkProduct (firstRowsB.toList) (((firstRowsB.toList).drop 120).take 20) (((firstBSquare).drop 120).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_square_batch07 :
    checkProduct (firstRowsB.toList) (((firstRowsB.toList).drop 140).take 20) (((firstBSquare).drop 140).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_square_batch08 :
    checkProduct (firstRowsB.toList) (((firstRowsB.toList).drop 160).take 20) (((firstBSquare).drop 160).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_square_batch09 :
    checkProduct (firstRowsB.toList) (((firstRowsB.toList).drop 180).take 20) (((firstBSquare).drop 180).take 20) = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_square_batch10 :
    checkProduct (firstRowsB.toList) (((firstRowsB.toList).drop 200).take 20) (((firstBSquare).drop 200).take 20) = true := by
  decide +kernel

private theorem firstB_square_rows : ∀ i : Fin 220,
    combine (firstRowsB.toList) (firstRowsB.toList)[i.val]! = (firstBSquare)[i.val]! := by
  apply forall_batches (blocks := 11) (size := 20) (by decide)
    (fun i => combine (firstRowsB.toList) (firstRowsB.toList)[i]! = (firstBSquare)[i]!)
  intro b j
  have h : checkProduct (firstRowsB.toList) (((firstRowsB.toList).drop (b.val * 20)).take 20) (((firstBSquare).drop (b.val * 20)).take 20) = true := by
    fin_cases b
    · exact firstB_square_batch00
    · exact firstB_square_batch01
    · exact firstB_square_batch02
    · exact firstB_square_batch03
    · exact firstB_square_batch04
    · exact firstB_square_batch05
    · exact firstB_square_batch06
    · exact firstB_square_batch07
    · exact firstB_square_batch08
    · exact firstB_square_batch09
    · exact firstB_square_batch10
  have he := checkProduct_sound (firstRowsB.toList) (((firstRowsB.toList).drop (b.val * 20)).take 20) (((firstBSquare).drop (b.val * 20)).take 20) h j.val
  simpa only [chunk_entry _ _ _ _ j.isLt] using he

theorem firstBSquare_matrix : matrix 220 220 firstBSquare = (matrixB false ^ 2).transpose := by
  have h := matrix_product_of_rows (m := 220) (n := 220) (p := 220)
    firstRowsB.toList firstRowsB.toList firstBSquare (by decide +kernel) firstB_square_rows
  simp only [matrix_array] at h
  change _ = ((decode 220 firstRowsB).transpose ^ 2).transpose
  rw [pow_two, Matrix.transpose_mul, Matrix.transpose_transpose]
  exact h.symm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.CertificateChecks
