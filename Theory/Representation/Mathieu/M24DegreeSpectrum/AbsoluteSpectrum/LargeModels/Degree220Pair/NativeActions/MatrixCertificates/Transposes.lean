module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.Rows

/-!
# Checked transposes of the four ATLAS matrices

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
private theorem firstA_batch00 :
    checkTranspose (firstRowsA.toList) (((firstA).drop 0).take 20) 0 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstA_batch01 :
    checkTranspose (firstRowsA.toList) (((firstA).drop 20).take 20) 20 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstA_batch02 :
    checkTranspose (firstRowsA.toList) (((firstA).drop 40).take 20) 40 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstA_batch03 :
    checkTranspose (firstRowsA.toList) (((firstA).drop 60).take 20) 60 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstA_batch04 :
    checkTranspose (firstRowsA.toList) (((firstA).drop 80).take 20) 80 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstA_batch05 :
    checkTranspose (firstRowsA.toList) (((firstA).drop 100).take 20) 100 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstA_batch06 :
    checkTranspose (firstRowsA.toList) (((firstA).drop 120).take 20) 120 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstA_batch07 :
    checkTranspose (firstRowsA.toList) (((firstA).drop 140).take 20) 140 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstA_batch08 :
    checkTranspose (firstRowsA.toList) (((firstA).drop 160).take 20) 160 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstA_batch09 :
    checkTranspose (firstRowsA.toList) (((firstA).drop 180).take 20) 180 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstA_batch10 :
    checkTranspose (firstRowsA.toList) (((firstA).drop 200).take 20) 200 = true := by
  decide +kernel

private theorem firstA_rows : ∀ i : Fin 220,
    column (firstRowsA.toList) i.val = (firstA)[i.val]! := by
  apply forall_batches (blocks := 11) (size := 20) (by decide)
    (fun i => column (firstRowsA.toList) i = (firstA)[i]!)
  intro b j
  have h : checkTranspose (firstRowsA.toList) (((firstA).drop (b.val * 20)).take 20) (b.val * 20) = true := by
    fin_cases b
    · exact firstA_batch00
    · exact firstA_batch01
    · exact firstA_batch02
    · exact firstA_batch03
    · exact firstA_batch04
    · exact firstA_batch05
    · exact firstA_batch06
    · exact firstA_batch07
    · exact firstA_batch08
    · exact firstA_batch09
    · exact firstA_batch10
  have hx : (firstA).length = 220 := by decide +kernel
  have hj : j.val < (((firstA).drop (b.val * 20)).take 20).length := by
    rw [chunk_length _ _ _ (by rw [hx]; have := b.isLt; omega)]
    exact j.isLt
  have he := checkTranspose_sound (firstRowsA.toList) (((firstA).drop (b.val * 20)).take 20) (b.val * 20) h j.val hj
  simpa only [chunk_entry _ _ _ _ j.isLt] using he

theorem firstA_matrix : matrix 220 220 firstA = matrixA false := by
  have h := matrix_transpose_of_rows (m := 220) (n := 220)
    firstRowsA.toList firstA (by decide +kernel) firstA_rows
  rw [matrix_array] at h
  exact h.symm

-- Keep the bounded kernel reductions sequential within this module.
set_option Elab.async false

set_option maxRecDepth 2048 in
private theorem firstB_batch00 :
    checkTranspose (firstRowsB.toList) (((firstB).drop 0).take 20) 0 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_batch01 :
    checkTranspose (firstRowsB.toList) (((firstB).drop 20).take 20) 20 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_batch02 :
    checkTranspose (firstRowsB.toList) (((firstB).drop 40).take 20) 40 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_batch03 :
    checkTranspose (firstRowsB.toList) (((firstB).drop 60).take 20) 60 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_batch04 :
    checkTranspose (firstRowsB.toList) (((firstB).drop 80).take 20) 80 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_batch05 :
    checkTranspose (firstRowsB.toList) (((firstB).drop 100).take 20) 100 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_batch06 :
    checkTranspose (firstRowsB.toList) (((firstB).drop 120).take 20) 120 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_batch07 :
    checkTranspose (firstRowsB.toList) (((firstB).drop 140).take 20) 140 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_batch08 :
    checkTranspose (firstRowsB.toList) (((firstB).drop 160).take 20) 160 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_batch09 :
    checkTranspose (firstRowsB.toList) (((firstB).drop 180).take 20) 180 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem firstB_batch10 :
    checkTranspose (firstRowsB.toList) (((firstB).drop 200).take 20) 200 = true := by
  decide +kernel

private theorem firstB_rows : ∀ i : Fin 220,
    column (firstRowsB.toList) i.val = (firstB)[i.val]! := by
  apply forall_batches (blocks := 11) (size := 20) (by decide)
    (fun i => column (firstRowsB.toList) i = (firstB)[i]!)
  intro b j
  have h : checkTranspose (firstRowsB.toList) (((firstB).drop (b.val * 20)).take 20) (b.val * 20) = true := by
    fin_cases b
    · exact firstB_batch00
    · exact firstB_batch01
    · exact firstB_batch02
    · exact firstB_batch03
    · exact firstB_batch04
    · exact firstB_batch05
    · exact firstB_batch06
    · exact firstB_batch07
    · exact firstB_batch08
    · exact firstB_batch09
    · exact firstB_batch10
  have hx : (firstB).length = 220 := by decide +kernel
  have hj : j.val < (((firstB).drop (b.val * 20)).take 20).length := by
    rw [chunk_length _ _ _ (by rw [hx]; have := b.isLt; omega)]
    exact j.isLt
  have he := checkTranspose_sound (firstRowsB.toList) (((firstB).drop (b.val * 20)).take 20) (b.val * 20) h j.val hj
  simpa only [chunk_entry _ _ _ _ j.isLt] using he

theorem firstB_matrix : matrix 220 220 firstB = matrixB false := by
  have h := matrix_transpose_of_rows (m := 220) (n := 220)
    firstRowsB.toList firstB (by decide +kernel) firstB_rows
  rw [matrix_array] at h
  exact h.symm

-- Keep the bounded kernel reductions sequential within this module.
set_option Elab.async false

set_option maxRecDepth 2048 in
private theorem secondA_batch00 :
    checkTranspose (secondRowsA.toList) (((secondA).drop 0).take 20) 0 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondA_batch01 :
    checkTranspose (secondRowsA.toList) (((secondA).drop 20).take 20) 20 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondA_batch02 :
    checkTranspose (secondRowsA.toList) (((secondA).drop 40).take 20) 40 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondA_batch03 :
    checkTranspose (secondRowsA.toList) (((secondA).drop 60).take 20) 60 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondA_batch04 :
    checkTranspose (secondRowsA.toList) (((secondA).drop 80).take 20) 80 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondA_batch05 :
    checkTranspose (secondRowsA.toList) (((secondA).drop 100).take 20) 100 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondA_batch06 :
    checkTranspose (secondRowsA.toList) (((secondA).drop 120).take 20) 120 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondA_batch07 :
    checkTranspose (secondRowsA.toList) (((secondA).drop 140).take 20) 140 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondA_batch08 :
    checkTranspose (secondRowsA.toList) (((secondA).drop 160).take 20) 160 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondA_batch09 :
    checkTranspose (secondRowsA.toList) (((secondA).drop 180).take 20) 180 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondA_batch10 :
    checkTranspose (secondRowsA.toList) (((secondA).drop 200).take 20) 200 = true := by
  decide +kernel

private theorem secondA_rows : ∀ i : Fin 220,
    column (secondRowsA.toList) i.val = (secondA)[i.val]! := by
  apply forall_batches (blocks := 11) (size := 20) (by decide)
    (fun i => column (secondRowsA.toList) i = (secondA)[i]!)
  intro b j
  have h : checkTranspose (secondRowsA.toList) (((secondA).drop (b.val * 20)).take 20) (b.val * 20) = true := by
    fin_cases b
    · exact secondA_batch00
    · exact secondA_batch01
    · exact secondA_batch02
    · exact secondA_batch03
    · exact secondA_batch04
    · exact secondA_batch05
    · exact secondA_batch06
    · exact secondA_batch07
    · exact secondA_batch08
    · exact secondA_batch09
    · exact secondA_batch10
  have hx : (secondA).length = 220 := by decide +kernel
  have hj : j.val < (((secondA).drop (b.val * 20)).take 20).length := by
    rw [chunk_length _ _ _ (by rw [hx]; have := b.isLt; omega)]
    exact j.isLt
  have he := checkTranspose_sound (secondRowsA.toList) (((secondA).drop (b.val * 20)).take 20) (b.val * 20) h j.val hj
  simpa only [chunk_entry _ _ _ _ j.isLt] using he

theorem secondA_matrix : matrix 220 220 secondA = matrixA true := by
  have h := matrix_transpose_of_rows (m := 220) (n := 220)
    secondRowsA.toList secondA (by decide +kernel) secondA_rows
  rw [matrix_array] at h
  exact h.symm

-- Keep the bounded kernel reductions sequential within this module.
set_option Elab.async false

set_option maxRecDepth 2048 in
private theorem secondB_batch00 :
    checkTranspose (secondRowsB.toList) (((secondB).drop 0).take 20) 0 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondB_batch01 :
    checkTranspose (secondRowsB.toList) (((secondB).drop 20).take 20) 20 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondB_batch02 :
    checkTranspose (secondRowsB.toList) (((secondB).drop 40).take 20) 40 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondB_batch03 :
    checkTranspose (secondRowsB.toList) (((secondB).drop 60).take 20) 60 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondB_batch04 :
    checkTranspose (secondRowsB.toList) (((secondB).drop 80).take 20) 80 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondB_batch05 :
    checkTranspose (secondRowsB.toList) (((secondB).drop 100).take 20) 100 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondB_batch06 :
    checkTranspose (secondRowsB.toList) (((secondB).drop 120).take 20) 120 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondB_batch07 :
    checkTranspose (secondRowsB.toList) (((secondB).drop 140).take 20) 140 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondB_batch08 :
    checkTranspose (secondRowsB.toList) (((secondB).drop 160).take 20) 160 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondB_batch09 :
    checkTranspose (secondRowsB.toList) (((secondB).drop 180).take 20) 180 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem secondB_batch10 :
    checkTranspose (secondRowsB.toList) (((secondB).drop 200).take 20) 200 = true := by
  decide +kernel

private theorem secondB_rows : ∀ i : Fin 220,
    column (secondRowsB.toList) i.val = (secondB)[i.val]! := by
  apply forall_batches (blocks := 11) (size := 20) (by decide)
    (fun i => column (secondRowsB.toList) i = (secondB)[i]!)
  intro b j
  have h : checkTranspose (secondRowsB.toList) (((secondB).drop (b.val * 20)).take 20) (b.val * 20) = true := by
    fin_cases b
    · exact secondB_batch00
    · exact secondB_batch01
    · exact secondB_batch02
    · exact secondB_batch03
    · exact secondB_batch04
    · exact secondB_batch05
    · exact secondB_batch06
    · exact secondB_batch07
    · exact secondB_batch08
    · exact secondB_batch09
    · exact secondB_batch10
  have hx : (secondB).length = 220 := by decide +kernel
  have hj : j.val < (((secondB).drop (b.val * 20)).take 20).length := by
    rw [chunk_length _ _ _ (by rw [hx]; have := b.isLt; omega)]
    exact j.isLt
  have he := checkTranspose_sound (secondRowsB.toList) (((secondB).drop (b.val * 20)).take 20) (b.val * 20) h j.val hj
  simpa only [chunk_entry _ _ _ _ j.isLt] using he

theorem secondB_matrix : matrix 220 220 secondB = matrixB true := by
  have h := matrix_transpose_of_rows (m := 220) (n := 220)
    secondRowsB.toList secondB (by decide +kernel) secondB_rows
  rw [matrix_array] at h
  exact h.symm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.CertificateChecks
