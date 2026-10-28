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

private theorem bRight_check00 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 0 16 = true := by
  decide +kernel

private theorem bRight_check01 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 16 16 = true := by
  decide +kernel

private theorem bRight_check02 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 32 16 = true := by
  decide +kernel

private theorem bRight_check03 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 48 16 = true := by
  decide +kernel

private theorem bRight_check04 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 64 16 = true := by
  decide +kernel

private theorem bRight_check05 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 80 16 = true := by
  decide +kernel

private theorem bRight_check06 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 96 16 = true := by
  decide +kernel

private theorem bRight_check07 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 112 16 = true := by
  decide +kernel

private theorem bRight_check08 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 128 16 = true := by
  decide +kernel

private theorem bRight_check09 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 144 16 = true := by
  decide +kernel

private theorem bRight_check10 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 160 16 = true := by
  decide +kernel

private theorem bRight_check11 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 176 16 = true := by
  decide +kernel

private theorem bRight_check12 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 192 16 = true := by
  decide +kernel

private theorem bRight_check13 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 208 16 = true := by
  decide +kernel

private theorem bRight_check14 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 224 16 = true := by
  decide +kernel

private theorem bRight_check15 :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 240 8 = true := by
  decide +kernel

private theorem bRight_check :
    checkRange (fun i => BinaryMatrix.listProduct seed6Rows[i]! atlasARows.toList 0 == bRightRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) bRight_check00
      (checkRange_append (m := 16) (n := 216) bRight_check01
      (checkRange_append (m := 16) (n := 200) bRight_check02
      (checkRange_append (m := 16) (n := 184) bRight_check03
      (checkRange_append (m := 16) (n := 168) bRight_check04
      (checkRange_append (m := 16) (n := 152) bRight_check05
      (checkRange_append (m := 16) (n := 136) bRight_check06
      (checkRange_append (m := 16) (n := 120) bRight_check07
      (checkRange_append (m := 16) (n := 104) bRight_check08
      (checkRange_append (m := 16) (n := 88) bRight_check09
      (checkRange_append (m := 16) (n := 72) bRight_check10
      (checkRange_append (m := 16) (n := 56) bRight_check11
      (checkRange_append (m := 16) (n := 40) bRight_check12
      (checkRange_append (m := 16) (n := 24) bRight_check13
      (checkRange_append (m := 16) (n := 8) bRight_check14
      bRight_check15)))))))))))))))

/-- Kernel-checked matrix product for `bRight`. -/
theorem bRight_product : BinaryMatrix.decode 248 seed6Rows *
    BinaryMatrix.decode 248 atlasARows = BinaryMatrix.decode 248 bRightRows :=
  checked_mul 248 seed6Rows atlasARows bRightRows (by decide) bRight_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
