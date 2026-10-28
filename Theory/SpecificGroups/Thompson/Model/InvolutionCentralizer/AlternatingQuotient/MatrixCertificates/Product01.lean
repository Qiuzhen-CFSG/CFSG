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

private theorem seed4_check00 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 0 16 = true := by
  decide +kernel

private theorem seed4_check01 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 16 16 = true := by
  decide +kernel

private theorem seed4_check02 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 32 16 = true := by
  decide +kernel

private theorem seed4_check03 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 48 16 = true := by
  decide +kernel

private theorem seed4_check04 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 64 16 = true := by
  decide +kernel

private theorem seed4_check05 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 80 16 = true := by
  decide +kernel

private theorem seed4_check06 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 96 16 = true := by
  decide +kernel

private theorem seed4_check07 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 112 16 = true := by
  decide +kernel

private theorem seed4_check08 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 128 16 = true := by
  decide +kernel

private theorem seed4_check09 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 144 16 = true := by
  decide +kernel

private theorem seed4_check10 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 160 16 = true := by
  decide +kernel

private theorem seed4_check11 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 176 16 = true := by
  decide +kernel

private theorem seed4_check12 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 192 16 = true := by
  decide +kernel

private theorem seed4_check13 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 208 16 = true := by
  decide +kernel

private theorem seed4_check14 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 224 16 = true := by
  decide +kernel

private theorem seed4_check15 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 240 8 = true := by
  decide +kernel

private theorem seed4_check :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! atlasBRows.toList 0 == seed4Rows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) seed4_check00
      (checkRange_append (m := 16) (n := 216) seed4_check01
      (checkRange_append (m := 16) (n := 200) seed4_check02
      (checkRange_append (m := 16) (n := 184) seed4_check03
      (checkRange_append (m := 16) (n := 168) seed4_check04
      (checkRange_append (m := 16) (n := 152) seed4_check05
      (checkRange_append (m := 16) (n := 136) seed4_check06
      (checkRange_append (m := 16) (n := 120) seed4_check07
      (checkRange_append (m := 16) (n := 104) seed4_check08
      (checkRange_append (m := 16) (n := 88) seed4_check09
      (checkRange_append (m := 16) (n := 72) seed4_check10
      (checkRange_append (m := 16) (n := 56) seed4_check11
      (checkRange_append (m := 16) (n := 40) seed4_check12
      (checkRange_append (m := 16) (n := 24) seed4_check13
      (checkRange_append (m := 16) (n := 8) seed4_check14
      seed4_check15)))))))))))))))

/-- Kernel-checked matrix product for `seed4`. -/
theorem seed4_product : BinaryMatrix.decode 248 seed3Rows *
    BinaryMatrix.decode 248 atlasBRows = BinaryMatrix.decode 248 seed4Rows :=
  checked_mul 248 seed3Rows atlasBRows seed4Rows (by decide) seed4_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
