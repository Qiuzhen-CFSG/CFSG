module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.Rows

/-!
# Checked ProjectionSection matrix identity

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
private theorem projection_section_batch00 :
    checkIdentity (sectionRows.toList) (((projectionRows.toList).drop 0).take 20) 0 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_section_batch01 :
    checkIdentity (sectionRows.toList) (((projectionRows.toList).drop 20).take 20) 20 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_section_batch02 :
    checkIdentity (sectionRows.toList) (((projectionRows.toList).drop 40).take 20) 40 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_section_batch03 :
    checkIdentity (sectionRows.toList) (((projectionRows.toList).drop 60).take 20) 60 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_section_batch04 :
    checkIdentity (sectionRows.toList) (((projectionRows.toList).drop 80).take 20) 80 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_section_batch05 :
    checkIdentity (sectionRows.toList) (((projectionRows.toList).drop 100).take 20) 100 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_section_batch06 :
    checkIdentity (sectionRows.toList) (((projectionRows.toList).drop 120).take 20) 120 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_section_batch07 :
    checkIdentity (sectionRows.toList) (((projectionRows.toList).drop 140).take 20) 140 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_section_batch08 :
    checkIdentity (sectionRows.toList) (((projectionRows.toList).drop 160).take 20) 160 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_section_batch09 :
    checkIdentity (sectionRows.toList) (((projectionRows.toList).drop 180).take 20) 180 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem projection_section_batch10 :
    checkIdentity (sectionRows.toList) (((projectionRows.toList).drop 200).take 20) 200 = true := by
  decide +kernel

private theorem projection_section_rows : ∀ i : Fin 220,
    combine (sectionRows.toList) (projectionRows.toList)[i.val]! = 2 ^ i.val := by
  apply forall_batches (blocks := 11) (size := 20) (by decide)
    (fun i => combine (sectionRows.toList) (projectionRows.toList)[i]! = 2 ^ i)
  intro b j
  have h : checkIdentity (sectionRows.toList) (((projectionRows.toList).drop (b.val * 20)).take 20) (b.val * 20) = true := by
    fin_cases b
    · exact projection_section_batch00
    · exact projection_section_batch01
    · exact projection_section_batch02
    · exact projection_section_batch03
    · exact projection_section_batch04
    · exact projection_section_batch05
    · exact projection_section_batch06
    · exact projection_section_batch07
    · exact projection_section_batch08
    · exact projection_section_batch09
    · exact projection_section_batch10
  have hx : (projectionRows.toList).length = 220 := by decide +kernel
  have hj : j.val < (((projectionRows.toList).drop (b.val * 20)).take 20).length := by
    rw [chunk_length _ _ _ (by rw [hx]; have := b.isLt; omega)]
    exact j.isLt
  have he := checkIdentity_sound (sectionRows.toList) (((projectionRows.toList).drop (b.val * 20)).take 20) (b.val * 20) h j.val hj
  simpa only [chunk_entry _ _ _ _ j.isLt] using he

theorem projection_section : projection * sectionMatrix = 1 := by
  have h := matrix_identity_of_rows (m := 220) (n := 462)
    projectionRows.toList sectionRows.toList (by decide +kernel) projection_section_rows
  simp only [matrix_array] at h
  exact h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.CertificateChecks
