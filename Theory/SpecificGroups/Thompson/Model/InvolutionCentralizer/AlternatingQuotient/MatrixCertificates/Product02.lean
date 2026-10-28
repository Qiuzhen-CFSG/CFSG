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

private theorem seed5_check00 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 0 16 = true := by
  decide +kernel

private theorem seed5_check01 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 16 16 = true := by
  decide +kernel

private theorem seed5_check02 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 32 16 = true := by
  decide +kernel

private theorem seed5_check03 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 48 16 = true := by
  decide +kernel

private theorem seed5_check04 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 64 16 = true := by
  decide +kernel

private theorem seed5_check05 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 80 16 = true := by
  decide +kernel

private theorem seed5_check06 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 96 16 = true := by
  decide +kernel

private theorem seed5_check07 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 112 16 = true := by
  decide +kernel

private theorem seed5_check08 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 128 16 = true := by
  decide +kernel

private theorem seed5_check09 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 144 16 = true := by
  decide +kernel

private theorem seed5_check10 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 160 16 = true := by
  decide +kernel

private theorem seed5_check11 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 176 16 = true := by
  decide +kernel

private theorem seed5_check12 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 192 16 = true := by
  decide +kernel

private theorem seed5_check13 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 208 16 = true := by
  decide +kernel

private theorem seed5_check14 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 224 16 = true := by
  decide +kernel

private theorem seed5_check15 :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 240 8 = true := by
  decide +kernel

private theorem seed5_check :
    checkRange (fun i => BinaryMatrix.listProduct seed3Rows[i]! seed4Rows.toList 0 == seed5Rows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) seed5_check00
      (checkRange_append (m := 16) (n := 216) seed5_check01
      (checkRange_append (m := 16) (n := 200) seed5_check02
      (checkRange_append (m := 16) (n := 184) seed5_check03
      (checkRange_append (m := 16) (n := 168) seed5_check04
      (checkRange_append (m := 16) (n := 152) seed5_check05
      (checkRange_append (m := 16) (n := 136) seed5_check06
      (checkRange_append (m := 16) (n := 120) seed5_check07
      (checkRange_append (m := 16) (n := 104) seed5_check08
      (checkRange_append (m := 16) (n := 88) seed5_check09
      (checkRange_append (m := 16) (n := 72) seed5_check10
      (checkRange_append (m := 16) (n := 56) seed5_check11
      (checkRange_append (m := 16) (n := 40) seed5_check12
      (checkRange_append (m := 16) (n := 24) seed5_check13
      (checkRange_append (m := 16) (n := 8) seed5_check14
      seed5_check15)))))))))))))))

/-- Kernel-checked matrix product for `seed5`. -/
theorem seed5_product : BinaryMatrix.decode 248 seed3Rows *
    BinaryMatrix.decode 248 seed4Rows = BinaryMatrix.decode 248 seed5Rows :=
  checked_mul 248 seed3Rows seed4Rows seed5Rows (by decide) seed5_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
