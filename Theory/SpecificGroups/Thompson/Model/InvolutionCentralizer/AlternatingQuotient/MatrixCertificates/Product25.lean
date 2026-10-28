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

private theorem wordATimesA_check00 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 0 16 = true := by
  decide +kernel

private theorem wordATimesA_check01 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 16 16 = true := by
  decide +kernel

private theorem wordATimesA_check02 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 32 16 = true := by
  decide +kernel

private theorem wordATimesA_check03 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 48 16 = true := by
  decide +kernel

private theorem wordATimesA_check04 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 64 16 = true := by
  decide +kernel

private theorem wordATimesA_check05 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 80 16 = true := by
  decide +kernel

private theorem wordATimesA_check06 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 96 16 = true := by
  decide +kernel

private theorem wordATimesA_check07 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 112 16 = true := by
  decide +kernel

private theorem wordATimesA_check08 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 128 16 = true := by
  decide +kernel

private theorem wordATimesA_check09 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 144 16 = true := by
  decide +kernel

private theorem wordATimesA_check10 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 160 16 = true := by
  decide +kernel

private theorem wordATimesA_check11 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 176 16 = true := by
  decide +kernel

private theorem wordATimesA_check12 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 192 16 = true := by
  decide +kernel

private theorem wordATimesA_check13 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 208 16 = true := by
  decide +kernel

private theorem wordATimesA_check14 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 224 16 = true := by
  decide +kernel

private theorem wordATimesA_check15 :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 240 8 = true := by
  decide +kernel

private theorem wordATimesA_check :
    checkRange (fun i => BinaryMatrix.listProduct wordARows[i]! atlasARows.toList 0 == wordATimesARows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) wordATimesA_check00
      (checkRange_append (m := 16) (n := 216) wordATimesA_check01
      (checkRange_append (m := 16) (n := 200) wordATimesA_check02
      (checkRange_append (m := 16) (n := 184) wordATimesA_check03
      (checkRange_append (m := 16) (n := 168) wordATimesA_check04
      (checkRange_append (m := 16) (n := 152) wordATimesA_check05
      (checkRange_append (m := 16) (n := 136) wordATimesA_check06
      (checkRange_append (m := 16) (n := 120) wordATimesA_check07
      (checkRange_append (m := 16) (n := 104) wordATimesA_check08
      (checkRange_append (m := 16) (n := 88) wordATimesA_check09
      (checkRange_append (m := 16) (n := 72) wordATimesA_check10
      (checkRange_append (m := 16) (n := 56) wordATimesA_check11
      (checkRange_append (m := 16) (n := 40) wordATimesA_check12
      (checkRange_append (m := 16) (n := 24) wordATimesA_check13
      (checkRange_append (m := 16) (n := 8) wordATimesA_check14
      wordATimesA_check15)))))))))))))))

/-- Kernel-checked matrix product for `wordATimesA`. -/
theorem wordATimesA_product : BinaryMatrix.decode 248 wordARows *
    BinaryMatrix.decode 248 atlasARows = BinaryMatrix.decode 248 wordATimesARows :=
  checked_mul 248 wordARows atlasARows wordATimesARows (by decide) wordATimesA_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
