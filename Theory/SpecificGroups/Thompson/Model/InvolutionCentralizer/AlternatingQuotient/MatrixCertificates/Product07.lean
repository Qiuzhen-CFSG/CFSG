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

private theorem bBase_check00 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 0 16 = true := by
  decide +kernel

private theorem bBase_check01 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 16 16 = true := by
  decide +kernel

private theorem bBase_check02 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 32 16 = true := by
  decide +kernel

private theorem bBase_check03 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 48 16 = true := by
  decide +kernel

private theorem bBase_check04 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 64 16 = true := by
  decide +kernel

private theorem bBase_check05 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 80 16 = true := by
  decide +kernel

private theorem bBase_check06 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 96 16 = true := by
  decide +kernel

private theorem bBase_check07 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 112 16 = true := by
  decide +kernel

private theorem bBase_check08 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 128 16 = true := by
  decide +kernel

private theorem bBase_check09 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 144 16 = true := by
  decide +kernel

private theorem bBase_check10 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 160 16 = true := by
  decide +kernel

private theorem bBase_check11 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 176 16 = true := by
  decide +kernel

private theorem bBase_check12 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 192 16 = true := by
  decide +kernel

private theorem bBase_check13 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 208 16 = true := by
  decide +kernel

private theorem bBase_check14 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 224 16 = true := by
  decide +kernel

private theorem bBase_check15 :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 240 8 = true := by
  decide +kernel

private theorem bBase_check :
    checkRange (fun i => BinaryMatrix.listProduct bInverseRows[i]! bLeftRows.toList 0 == bBaseRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) bBase_check00
      (checkRange_append (m := 16) (n := 216) bBase_check01
      (checkRange_append (m := 16) (n := 200) bBase_check02
      (checkRange_append (m := 16) (n := 184) bBase_check03
      (checkRange_append (m := 16) (n := 168) bBase_check04
      (checkRange_append (m := 16) (n := 152) bBase_check05
      (checkRange_append (m := 16) (n := 136) bBase_check06
      (checkRange_append (m := 16) (n := 120) bBase_check07
      (checkRange_append (m := 16) (n := 104) bBase_check08
      (checkRange_append (m := 16) (n := 88) bBase_check09
      (checkRange_append (m := 16) (n := 72) bBase_check10
      (checkRange_append (m := 16) (n := 56) bBase_check11
      (checkRange_append (m := 16) (n := 40) bBase_check12
      (checkRange_append (m := 16) (n := 24) bBase_check13
      (checkRange_append (m := 16) (n := 8) bBase_check14
      bBase_check15)))))))))))))))

/-- Kernel-checked matrix product for `bBase`. -/
theorem bBase_product : BinaryMatrix.decode 248 bInverseRows *
    BinaryMatrix.decode 248 bLeftRows = BinaryMatrix.decode 248 bBaseRows :=
  checked_mul 248 bInverseRows bLeftRows bBaseRows (by decide) bBase_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
