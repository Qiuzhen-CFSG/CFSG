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

private theorem bPower2_check00 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 0 16 = true := by
  decide +kernel

private theorem bPower2_check01 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 16 16 = true := by
  decide +kernel

private theorem bPower2_check02 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 32 16 = true := by
  decide +kernel

private theorem bPower2_check03 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 48 16 = true := by
  decide +kernel

private theorem bPower2_check04 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 64 16 = true := by
  decide +kernel

private theorem bPower2_check05 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 80 16 = true := by
  decide +kernel

private theorem bPower2_check06 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 96 16 = true := by
  decide +kernel

private theorem bPower2_check07 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 112 16 = true := by
  decide +kernel

private theorem bPower2_check08 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 128 16 = true := by
  decide +kernel

private theorem bPower2_check09 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 144 16 = true := by
  decide +kernel

private theorem bPower2_check10 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 160 16 = true := by
  decide +kernel

private theorem bPower2_check11 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 176 16 = true := by
  decide +kernel

private theorem bPower2_check12 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 192 16 = true := by
  decide +kernel

private theorem bPower2_check13 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 208 16 = true := by
  decide +kernel

private theorem bPower2_check14 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 224 16 = true := by
  decide +kernel

private theorem bPower2_check15 :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 240 8 = true := by
  decide +kernel

private theorem bPower2_check :
    checkRange (fun i => BinaryMatrix.listProduct bBaseRows[i]! bBaseRows.toList 0 == bPower2Rows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) bPower2_check00
      (checkRange_append (m := 16) (n := 216) bPower2_check01
      (checkRange_append (m := 16) (n := 200) bPower2_check02
      (checkRange_append (m := 16) (n := 184) bPower2_check03
      (checkRange_append (m := 16) (n := 168) bPower2_check04
      (checkRange_append (m := 16) (n := 152) bPower2_check05
      (checkRange_append (m := 16) (n := 136) bPower2_check06
      (checkRange_append (m := 16) (n := 120) bPower2_check07
      (checkRange_append (m := 16) (n := 104) bPower2_check08
      (checkRange_append (m := 16) (n := 88) bPower2_check09
      (checkRange_append (m := 16) (n := 72) bPower2_check10
      (checkRange_append (m := 16) (n := 56) bPower2_check11
      (checkRange_append (m := 16) (n := 40) bPower2_check12
      (checkRange_append (m := 16) (n := 24) bPower2_check13
      (checkRange_append (m := 16) (n := 8) bPower2_check14
      bPower2_check15)))))))))))))))

/-- Kernel-checked matrix product for `bPower2`. -/
theorem bPower2_product : BinaryMatrix.decode 248 bBaseRows *
    BinaryMatrix.decode 248 bBaseRows = BinaryMatrix.decode 248 bPower2Rows :=
  checked_mul 248 bBaseRows bBaseRows bPower2Rows (by decide) bPower2_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
