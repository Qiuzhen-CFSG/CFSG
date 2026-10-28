module

public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Rows
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Checker

/-!
# Checked matrices for the Thompson max3 words

Packed rows retain the ATLAS multiplication orientation. The two inverse
steps are justified by product-to-identity certificates. Product checks use
small row intervals and the proved list-product decoder; Python supplies
witnesses only. No recognition, order, or simplicity theorem is used.

Source: ATLAS `ThG1-max3W1` (Wilson, Nickerson and Bray), preserved in
`AlternatingQuotient/source/`; see GLS3 Table 5.3x. Reproduction and benchmark
notes are in `MatrixCertificates/source/`.
-/

public section
namespace Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates

-- The measured sixteen-row checks are kept sequential to bound peak memory.
set_option Elab.async false
set_option maxRecDepth 2048

private theorem middle_check00 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 0 16 = true := by
  decide +kernel

private theorem middle_check01 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 16 16 = true := by
  decide +kernel

private theorem middle_check02 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 32 16 = true := by
  decide +kernel

private theorem middle_check03 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 48 16 = true := by
  decide +kernel

private theorem middle_check04 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 64 16 = true := by
  decide +kernel

private theorem middle_check05 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 80 16 = true := by
  decide +kernel

private theorem middle_check06 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 96 16 = true := by
  decide +kernel

private theorem middle_check07 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 112 16 = true := by
  decide +kernel

private theorem middle_check08 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 128 16 = true := by
  decide +kernel

private theorem middle_check09 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 144 16 = true := by
  decide +kernel

private theorem middle_check10 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 160 16 = true := by
  decide +kernel

private theorem middle_check11 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 176 16 = true := by
  decide +kernel

private theorem middle_check12 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 192 16 = true := by
  decide +kernel

private theorem middle_check13 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 208 16 = true := by
  decide +kernel

private theorem middle_check14 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 224 16 = true := by
  decide +kernel

private theorem middle_check15 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 240 8 = true := by
  decide +kernel

private theorem middle_check :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! seed5Rows.toList 0 == middleRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) middle_check00
      (checkRange_append (m := 16) (n := 216) middle_check01
      (checkRange_append (m := 16) (n := 200) middle_check02
      (checkRange_append (m := 16) (n := 184) middle_check03
      (checkRange_append (m := 16) (n := 168) middle_check04
      (checkRange_append (m := 16) (n := 152) middle_check05
      (checkRange_append (m := 16) (n := 136) middle_check06
      (checkRange_append (m := 16) (n := 120) middle_check07
      (checkRange_append (m := 16) (n := 104) middle_check08
      (checkRange_append (m := 16) (n := 88) middle_check09
      (checkRange_append (m := 16) (n := 72) middle_check10
      (checkRange_append (m := 16) (n := 56) middle_check11
      (checkRange_append (m := 16) (n := 40) middle_check12
      (checkRange_append (m := 16) (n := 24) middle_check13
      (checkRange_append (m := 16) (n := 8) middle_check14
      middle_check15)))))))))))))))

/-- Kernel-checked matrix product for `middle`. -/
theorem middle_product : BinaryMatrix.decode 248 seed6Rows *
    BinaryMatrix.decode 248 seed5Rows = BinaryMatrix.decode 248 middleRows :=
  checked_mul 248 seed6Rows seed5Rows middleRows (by decide) middle_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
