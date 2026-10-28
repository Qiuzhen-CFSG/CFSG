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

private theorem wordB_check00 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 0 16 = true := by
  decide +kernel

private theorem wordB_check01 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 16 16 = true := by
  decide +kernel

private theorem wordB_check02 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 32 16 = true := by
  decide +kernel

private theorem wordB_check03 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 48 16 = true := by
  decide +kernel

private theorem wordB_check04 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 64 16 = true := by
  decide +kernel

private theorem wordB_check05 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 80 16 = true := by
  decide +kernel

private theorem wordB_check06 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 96 16 = true := by
  decide +kernel

private theorem wordB_check07 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 112 16 = true := by
  decide +kernel

private theorem wordB_check08 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 128 16 = true := by
  decide +kernel

private theorem wordB_check09 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 144 16 = true := by
  decide +kernel

private theorem wordB_check10 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 160 16 = true := by
  decide +kernel

private theorem wordB_check11 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 176 16 = true := by
  decide +kernel

private theorem wordB_check12 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 192 16 = true := by
  decide +kernel

private theorem wordB_check13 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 208 16 = true := by
  decide +kernel

private theorem wordB_check14 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 224 16 = true := by
  decide +kernel

private theorem wordB_check15 :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 240 8 = true := by
  decide +kernel

private theorem wordB_check :
    checkRange (fun i => BinaryMatrix.listProduct bLeftRows[i]! bPower9Rows.toList 0 == wordBRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) wordB_check00
      (checkRange_append (m := 16) (n := 216) wordB_check01
      (checkRange_append (m := 16) (n := 200) wordB_check02
      (checkRange_append (m := 16) (n := 184) wordB_check03
      (checkRange_append (m := 16) (n := 168) wordB_check04
      (checkRange_append (m := 16) (n := 152) wordB_check05
      (checkRange_append (m := 16) (n := 136) wordB_check06
      (checkRange_append (m := 16) (n := 120) wordB_check07
      (checkRange_append (m := 16) (n := 104) wordB_check08
      (checkRange_append (m := 16) (n := 88) wordB_check09
      (checkRange_append (m := 16) (n := 72) wordB_check10
      (checkRange_append (m := 16) (n := 56) wordB_check11
      (checkRange_append (m := 16) (n := 40) wordB_check12
      (checkRange_append (m := 16) (n := 24) wordB_check13
      (checkRange_append (m := 16) (n := 8) wordB_check14
      wordB_check15)))))))))))))))

/-- Kernel-checked matrix product for `wordB`. -/
theorem wordB_product : BinaryMatrix.decode 248 bLeftRows *
    BinaryMatrix.decode 248 bPower9Rows = BinaryMatrix.decode 248 wordBRows :=
  checked_mul 248 bLeftRows bPower9Rows wordBRows (by decide) wordB_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
