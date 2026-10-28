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

private theorem wordA_check00 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 0 16 = true := by
  decide +kernel

private theorem wordA_check01 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 16 16 = true := by
  decide +kernel

private theorem wordA_check02 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 32 16 = true := by
  decide +kernel

private theorem wordA_check03 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 48 16 = true := by
  decide +kernel

private theorem wordA_check04 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 64 16 = true := by
  decide +kernel

private theorem wordA_check05 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 80 16 = true := by
  decide +kernel

private theorem wordA_check06 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 96 16 = true := by
  decide +kernel

private theorem wordA_check07 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 112 16 = true := by
  decide +kernel

private theorem wordA_check08 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 128 16 = true := by
  decide +kernel

private theorem wordA_check09 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 144 16 = true := by
  decide +kernel

private theorem wordA_check10 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 160 16 = true := by
  decide +kernel

private theorem wordA_check11 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 176 16 = true := by
  decide +kernel

private theorem wordA_check12 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 192 16 = true := by
  decide +kernel

private theorem wordA_check13 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 208 16 = true := by
  decide +kernel

private theorem wordA_check14 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 224 16 = true := by
  decide +kernel

private theorem wordA_check15 :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 240 8 = true := by
  decide +kernel

private theorem wordA_check :
    checkRange (fun i => BinaryMatrix.listProduct aPower7Rows[i]! aPower7Rows.toList 0 == wordARows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) wordA_check00
      (checkRange_append (m := 16) (n := 216) wordA_check01
      (checkRange_append (m := 16) (n := 200) wordA_check02
      (checkRange_append (m := 16) (n := 184) wordA_check03
      (checkRange_append (m := 16) (n := 168) wordA_check04
      (checkRange_append (m := 16) (n := 152) wordA_check05
      (checkRange_append (m := 16) (n := 136) wordA_check06
      (checkRange_append (m := 16) (n := 120) wordA_check07
      (checkRange_append (m := 16) (n := 104) wordA_check08
      (checkRange_append (m := 16) (n := 88) wordA_check09
      (checkRange_append (m := 16) (n := 72) wordA_check10
      (checkRange_append (m := 16) (n := 56) wordA_check11
      (checkRange_append (m := 16) (n := 40) wordA_check12
      (checkRange_append (m := 16) (n := 24) wordA_check13
      (checkRange_append (m := 16) (n := 8) wordA_check14
      wordA_check15)))))))))))))))

/-- Kernel-checked matrix product for `wordA`. -/
theorem wordA_product : BinaryMatrix.decode 248 aPower7Rows *
    BinaryMatrix.decode 248 aPower7Rows = BinaryMatrix.decode 248 wordARows :=
  checked_mul 248 aPower7Rows aPower7Rows wordARows (by decide) wordA_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
