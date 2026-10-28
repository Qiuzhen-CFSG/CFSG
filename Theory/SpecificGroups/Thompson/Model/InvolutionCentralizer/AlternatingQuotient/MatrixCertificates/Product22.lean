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

private theorem aPower6_check00 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 0 16 = true := by
  decide +kernel

private theorem aPower6_check01 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 16 16 = true := by
  decide +kernel

private theorem aPower6_check02 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 32 16 = true := by
  decide +kernel

private theorem aPower6_check03 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 48 16 = true := by
  decide +kernel

private theorem aPower6_check04 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 64 16 = true := by
  decide +kernel

private theorem aPower6_check05 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 80 16 = true := by
  decide +kernel

private theorem aPower6_check06 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 96 16 = true := by
  decide +kernel

private theorem aPower6_check07 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 112 16 = true := by
  decide +kernel

private theorem aPower6_check08 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 128 16 = true := by
  decide +kernel

private theorem aPower6_check09 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 144 16 = true := by
  decide +kernel

private theorem aPower6_check10 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 160 16 = true := by
  decide +kernel

private theorem aPower6_check11 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 176 16 = true := by
  decide +kernel

private theorem aPower6_check12 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 192 16 = true := by
  decide +kernel

private theorem aPower6_check13 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 208 16 = true := by
  decide +kernel

private theorem aPower6_check14 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 224 16 = true := by
  decide +kernel

private theorem aPower6_check15 :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 240 8 = true := by
  decide +kernel

private theorem aPower6_check :
    checkRange (fun i => BinaryMatrix.listProduct aPower3Rows[i]! aPower3Rows.toList 0 == aPower6Rows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) aPower6_check00
      (checkRange_append (m := 16) (n := 216) aPower6_check01
      (checkRange_append (m := 16) (n := 200) aPower6_check02
      (checkRange_append (m := 16) (n := 184) aPower6_check03
      (checkRange_append (m := 16) (n := 168) aPower6_check04
      (checkRange_append (m := 16) (n := 152) aPower6_check05
      (checkRange_append (m := 16) (n := 136) aPower6_check06
      (checkRange_append (m := 16) (n := 120) aPower6_check07
      (checkRange_append (m := 16) (n := 104) aPower6_check08
      (checkRange_append (m := 16) (n := 88) aPower6_check09
      (checkRange_append (m := 16) (n := 72) aPower6_check10
      (checkRange_append (m := 16) (n := 56) aPower6_check11
      (checkRange_append (m := 16) (n := 40) aPower6_check12
      (checkRange_append (m := 16) (n := 24) aPower6_check13
      (checkRange_append (m := 16) (n := 8) aPower6_check14
      aPower6_check15)))))))))))))))

/-- Kernel-checked matrix product for `aPower6`. -/
theorem aPower6_product : BinaryMatrix.decode 248 aPower3Rows *
    BinaryMatrix.decode 248 aPower3Rows = BinaryMatrix.decode 248 aPower6Rows :=
  checked_mul 248 aPower3Rows aPower3Rows aPower6Rows (by decide) aPower6_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
