module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.MatrixCertificates.Rows
public import Mathlib.Data.Matrix.Basic

/-!
# Checked DualInverse matrix identity

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
private theorem dual_left_batch00 :
    checkIdentity (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop 0).take 20) 0 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_left_batch01 :
    checkIdentity (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop 20).take 20) 20 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_left_batch02 :
    checkIdentity (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop 40).take 20) 40 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_left_batch03 :
    checkIdentity (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop 60).take 20) 60 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_left_batch04 :
    checkIdentity (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop 80).take 20) 80 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_left_batch05 :
    checkIdentity (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop 100).take 20) 100 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_left_batch06 :
    checkIdentity (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop 120).take 20) 120 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_left_batch07 :
    checkIdentity (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop 140).take 20) 140 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_left_batch08 :
    checkIdentity (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop 160).take 20) 160 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_left_batch09 :
    checkIdentity (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop 180).take 20) 180 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem dual_left_batch10 :
    checkIdentity (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop 200).take 20) 200 = true := by
  decide +kernel

private theorem dual_left_rows : ∀ i : Fin 220,
    combine (dualChangeInverseRows.toList) (dualChangeRows.toList)[i.val]! = 2 ^ i.val := by
  apply forall_batches (blocks := 11) (size := 20) (by decide)
    (fun i => combine (dualChangeInverseRows.toList) (dualChangeRows.toList)[i]! = 2 ^ i)
  intro b j
  have h : checkIdentity (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop (b.val * 20)).take 20) (b.val * 20) = true := by
    fin_cases b
    · exact dual_left_batch00
    · exact dual_left_batch01
    · exact dual_left_batch02
    · exact dual_left_batch03
    · exact dual_left_batch04
    · exact dual_left_batch05
    · exact dual_left_batch06
    · exact dual_left_batch07
    · exact dual_left_batch08
    · exact dual_left_batch09
    · exact dual_left_batch10
  have hx : (dualChangeRows.toList).length = 220 := by decide +kernel
  have hj : j.val < (((dualChangeRows.toList).drop (b.val * 20)).take 20).length := by
    rw [chunk_length _ _ _ (by rw [hx]; have := b.isLt; omega)]
    exact j.isLt
  have he := checkIdentity_sound (dualChangeInverseRows.toList) (((dualChangeRows.toList).drop (b.val * 20)).take 20) (b.val * 20) h j.val hj
  simpa only [chunk_entry _ _ _ _ j.isLt] using he

theorem dual_left : dualChange * dualChangeInverse = 1 := by
  have h := matrix_identity_of_rows (m := 220) (n := 220)
    dualChangeRows.toList dualChangeInverseRows.toList (by decide +kernel) dual_left_rows
  simp only [matrix_array] at h
  exact h

theorem dual_right : dualChangeInverse * dualChange = 1 :=
  (mul_eq_one_comm (a := dualChange) (b := dualChangeInverse)).mp dual_left

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.CertificateChecks
