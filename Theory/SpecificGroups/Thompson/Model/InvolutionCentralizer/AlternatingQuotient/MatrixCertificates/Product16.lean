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

private theorem aLeft_check00 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 0 16 = true := by
  decide +kernel

private theorem aLeft_check01 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 16 16 = true := by
  decide +kernel

private theorem aLeft_check02 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 32 16 = true := by
  decide +kernel

private theorem aLeft_check03 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 48 16 = true := by
  decide +kernel

private theorem aLeft_check04 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 64 16 = true := by
  decide +kernel

private theorem aLeft_check05 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 80 16 = true := by
  decide +kernel

private theorem aLeft_check06 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 96 16 = true := by
  decide +kernel

private theorem aLeft_check07 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 112 16 = true := by
  decide +kernel

private theorem aLeft_check08 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 128 16 = true := by
  decide +kernel

private theorem aLeft_check09 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 144 16 = true := by
  decide +kernel

private theorem aLeft_check10 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 160 16 = true := by
  decide +kernel

private theorem aLeft_check11 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 176 16 = true := by
  decide +kernel

private theorem aLeft_check12 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 192 16 = true := by
  decide +kernel

private theorem aLeft_check13 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 208 16 = true := by
  decide +kernel

private theorem aLeft_check14 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 224 16 = true := by
  decide +kernel

private theorem aLeft_check15 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 240 8 = true := by
  decide +kernel

private theorem aLeft_check :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed10Rows.toList 0 == aLeftRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) aLeft_check00
      (checkRange_append (m := 16) (n := 216) aLeft_check01
      (checkRange_append (m := 16) (n := 200) aLeft_check02
      (checkRange_append (m := 16) (n := 184) aLeft_check03
      (checkRange_append (m := 16) (n := 168) aLeft_check04
      (checkRange_append (m := 16) (n := 152) aLeft_check05
      (checkRange_append (m := 16) (n := 136) aLeft_check06
      (checkRange_append (m := 16) (n := 120) aLeft_check07
      (checkRange_append (m := 16) (n := 104) aLeft_check08
      (checkRange_append (m := 16) (n := 88) aLeft_check09
      (checkRange_append (m := 16) (n := 72) aLeft_check10
      (checkRange_append (m := 16) (n := 56) aLeft_check11
      (checkRange_append (m := 16) (n := 40) aLeft_check12
      (checkRange_append (m := 16) (n := 24) aLeft_check13
      (checkRange_append (m := 16) (n := 8) aLeft_check14
      aLeft_check15)))))))))))))))

/-- Kernel-checked matrix product for `aLeft`. -/
theorem aLeft_product : BinaryMatrix.decode 248 atlasARows *
    BinaryMatrix.decode 248 seed10Rows = BinaryMatrix.decode 248 aLeftRows :=
  checked_mul 248 atlasARows seed10Rows aLeftRows (by decide) aLeft_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
