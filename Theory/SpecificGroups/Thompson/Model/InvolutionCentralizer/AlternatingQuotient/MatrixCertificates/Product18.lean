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

private theorem aInverse_right_inverse_check00 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 0 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check01 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 16 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check02 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 32 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check03 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 48 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check04 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 64 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check05 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 80 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check06 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 96 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check07 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 112 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check08 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 128 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check09 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 144 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check10 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 160 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check11 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 176 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check12 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 192 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check13 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 208 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check14 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 224 16 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check15 :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 240 8 = true := by
  decide +kernel

private theorem aInverse_right_inverse_check :
    checkRange (fun i => BinaryMatrix.listProduct aRightRows[i]! aInverseRows.toList 0 == 2 ^ i) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) aInverse_right_inverse_check00
      (checkRange_append (m := 16) (n := 216) aInverse_right_inverse_check01
      (checkRange_append (m := 16) (n := 200) aInverse_right_inverse_check02
      (checkRange_append (m := 16) (n := 184) aInverse_right_inverse_check03
      (checkRange_append (m := 16) (n := 168) aInverse_right_inverse_check04
      (checkRange_append (m := 16) (n := 152) aInverse_right_inverse_check05
      (checkRange_append (m := 16) (n := 136) aInverse_right_inverse_check06
      (checkRange_append (m := 16) (n := 120) aInverse_right_inverse_check07
      (checkRange_append (m := 16) (n := 104) aInverse_right_inverse_check08
      (checkRange_append (m := 16) (n := 88) aInverse_right_inverse_check09
      (checkRange_append (m := 16) (n := 72) aInverse_right_inverse_check10
      (checkRange_append (m := 16) (n := 56) aInverse_right_inverse_check11
      (checkRange_append (m := 16) (n := 40) aInverse_right_inverse_check12
      (checkRange_append (m := 16) (n := 24) aInverse_right_inverse_check13
      (checkRange_append (m := 16) (n := 8) aInverse_right_inverse_check14
      aInverse_right_inverse_check15)))))))))))))))

/-- Kernel-checked matrix product for `aInverse_right_inverse`. -/
theorem aInverse_right_inverse_product : BinaryMatrix.decode 248 aRightRows *
    BinaryMatrix.decode 248 aInverseRows = 1 :=
  checked_mul_one 248 aRightRows aInverseRows (by decide) aInverse_right_inverse_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
