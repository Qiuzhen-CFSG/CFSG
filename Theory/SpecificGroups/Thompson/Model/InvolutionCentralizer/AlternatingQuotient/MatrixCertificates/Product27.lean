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

private theorem wordBTimesA_check00 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 0 16 = true := by
  decide +kernel

private theorem wordBTimesA_check01 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 16 16 = true := by
  decide +kernel

private theorem wordBTimesA_check02 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 32 16 = true := by
  decide +kernel

private theorem wordBTimesA_check03 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 48 16 = true := by
  decide +kernel

private theorem wordBTimesA_check04 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 64 16 = true := by
  decide +kernel

private theorem wordBTimesA_check05 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 80 16 = true := by
  decide +kernel

private theorem wordBTimesA_check06 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 96 16 = true := by
  decide +kernel

private theorem wordBTimesA_check07 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 112 16 = true := by
  decide +kernel

private theorem wordBTimesA_check08 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 128 16 = true := by
  decide +kernel

private theorem wordBTimesA_check09 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 144 16 = true := by
  decide +kernel

private theorem wordBTimesA_check10 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 160 16 = true := by
  decide +kernel

private theorem wordBTimesA_check11 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 176 16 = true := by
  decide +kernel

private theorem wordBTimesA_check12 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 192 16 = true := by
  decide +kernel

private theorem wordBTimesA_check13 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 208 16 = true := by
  decide +kernel

private theorem wordBTimesA_check14 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 224 16 = true := by
  decide +kernel

private theorem wordBTimesA_check15 :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 240 8 = true := by
  decide +kernel

private theorem wordBTimesA_check :
    checkRange (fun i => BinaryMatrix.listProduct wordBRows[i]! atlasARows.toList 0 == wordBTimesARows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) wordBTimesA_check00
      (checkRange_append (m := 16) (n := 216) wordBTimesA_check01
      (checkRange_append (m := 16) (n := 200) wordBTimesA_check02
      (checkRange_append (m := 16) (n := 184) wordBTimesA_check03
      (checkRange_append (m := 16) (n := 168) wordBTimesA_check04
      (checkRange_append (m := 16) (n := 152) wordBTimesA_check05
      (checkRange_append (m := 16) (n := 136) wordBTimesA_check06
      (checkRange_append (m := 16) (n := 120) wordBTimesA_check07
      (checkRange_append (m := 16) (n := 104) wordBTimesA_check08
      (checkRange_append (m := 16) (n := 88) wordBTimesA_check09
      (checkRange_append (m := 16) (n := 72) wordBTimesA_check10
      (checkRange_append (m := 16) (n := 56) wordBTimesA_check11
      (checkRange_append (m := 16) (n := 40) wordBTimesA_check12
      (checkRange_append (m := 16) (n := 24) wordBTimesA_check13
      (checkRange_append (m := 16) (n := 8) wordBTimesA_check14
      wordBTimesA_check15)))))))))))))))

/-- Kernel-checked matrix product for `wordBTimesA`. -/
theorem wordBTimesA_product : BinaryMatrix.decode 248 wordBRows *
    BinaryMatrix.decode 248 atlasARows = BinaryMatrix.decode 248 wordBTimesARows :=
  checked_mul 248 wordBRows atlasARows wordBTimesARows (by decide) wordBTimesA_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
