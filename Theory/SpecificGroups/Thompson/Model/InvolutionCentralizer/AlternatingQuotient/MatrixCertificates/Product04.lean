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

private theorem bLeft_check00 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 0 16 = true := by
  decide +kernel

private theorem bLeft_check01 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 16 16 = true := by
  decide +kernel

private theorem bLeft_check02 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 32 16 = true := by
  decide +kernel

private theorem bLeft_check03 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 48 16 = true := by
  decide +kernel

private theorem bLeft_check04 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 64 16 = true := by
  decide +kernel

private theorem bLeft_check05 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 80 16 = true := by
  decide +kernel

private theorem bLeft_check06 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 96 16 = true := by
  decide +kernel

private theorem bLeft_check07 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 112 16 = true := by
  decide +kernel

private theorem bLeft_check08 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 128 16 = true := by
  decide +kernel

private theorem bLeft_check09 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 144 16 = true := by
  decide +kernel

private theorem bLeft_check10 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 160 16 = true := by
  decide +kernel

private theorem bLeft_check11 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 176 16 = true := by
  decide +kernel

private theorem bLeft_check12 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 192 16 = true := by
  decide +kernel

private theorem bLeft_check13 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 208 16 = true := by
  decide +kernel

private theorem bLeft_check14 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 224 16 = true := by
  decide +kernel

private theorem bLeft_check15 :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 240 8 = true := by
  decide +kernel

private theorem bLeft_check :
    checkRange (fun i => BinaryMatrix.listProduct atlasARows[i]! seed6Rows.toList 0 == bLeftRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) bLeft_check00
      (checkRange_append (m := 16) (n := 216) bLeft_check01
      (checkRange_append (m := 16) (n := 200) bLeft_check02
      (checkRange_append (m := 16) (n := 184) bLeft_check03
      (checkRange_append (m := 16) (n := 168) bLeft_check04
      (checkRange_append (m := 16) (n := 152) bLeft_check05
      (checkRange_append (m := 16) (n := 136) bLeft_check06
      (checkRange_append (m := 16) (n := 120) bLeft_check07
      (checkRange_append (m := 16) (n := 104) bLeft_check08
      (checkRange_append (m := 16) (n := 88) bLeft_check09
      (checkRange_append (m := 16) (n := 72) bLeft_check10
      (checkRange_append (m := 16) (n := 56) bLeft_check11
      (checkRange_append (m := 16) (n := 40) bLeft_check12
      (checkRange_append (m := 16) (n := 24) bLeft_check13
      (checkRange_append (m := 16) (n := 8) bLeft_check14
      bLeft_check15)))))))))))))))

/-- Kernel-checked matrix product for `bLeft`. -/
theorem bLeft_product : BinaryMatrix.decode 248 atlasARows *
    BinaryMatrix.decode 248 seed6Rows = BinaryMatrix.decode 248 bLeftRows :=
  checked_mul 248 atlasARows seed6Rows bLeftRows (by decide) bLeft_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
