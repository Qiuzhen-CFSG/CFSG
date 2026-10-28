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

private theorem aBase_check00 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 0 16 = true := by
  decide +kernel

private theorem aBase_check01 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 16 16 = true := by
  decide +kernel

private theorem aBase_check02 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 32 16 = true := by
  decide +kernel

private theorem aBase_check03 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 48 16 = true := by
  decide +kernel

private theorem aBase_check04 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 64 16 = true := by
  decide +kernel

private theorem aBase_check05 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 80 16 = true := by
  decide +kernel

private theorem aBase_check06 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 96 16 = true := by
  decide +kernel

private theorem aBase_check07 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 112 16 = true := by
  decide +kernel

private theorem aBase_check08 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 128 16 = true := by
  decide +kernel

private theorem aBase_check09 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 144 16 = true := by
  decide +kernel

private theorem aBase_check10 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 160 16 = true := by
  decide +kernel

private theorem aBase_check11 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 176 16 = true := by
  decide +kernel

private theorem aBase_check12 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 192 16 = true := by
  decide +kernel

private theorem aBase_check13 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 208 16 = true := by
  decide +kernel

private theorem aBase_check14 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 224 16 = true := by
  decide +kernel

private theorem aBase_check15 :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 240 8 = true := by
  decide +kernel

private theorem aBase_check :
    checkRange (fun i => BinaryMatrix.listProduct aInverseRows[i]! aLeftRows.toList 0 == aBaseRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) aBase_check00
      (checkRange_append (m := 16) (n := 216) aBase_check01
      (checkRange_append (m := 16) (n := 200) aBase_check02
      (checkRange_append (m := 16) (n := 184) aBase_check03
      (checkRange_append (m := 16) (n := 168) aBase_check04
      (checkRange_append (m := 16) (n := 152) aBase_check05
      (checkRange_append (m := 16) (n := 136) aBase_check06
      (checkRange_append (m := 16) (n := 120) aBase_check07
      (checkRange_append (m := 16) (n := 104) aBase_check08
      (checkRange_append (m := 16) (n := 88) aBase_check09
      (checkRange_append (m := 16) (n := 72) aBase_check10
      (checkRange_append (m := 16) (n := 56) aBase_check11
      (checkRange_append (m := 16) (n := 40) aBase_check12
      (checkRange_append (m := 16) (n := 24) aBase_check13
      (checkRange_append (m := 16) (n := 8) aBase_check14
      aBase_check15)))))))))))))))

/-- Kernel-checked matrix product for `aBase`. -/
theorem aBase_product : BinaryMatrix.decode 248 aInverseRows *
    BinaryMatrix.decode 248 aLeftRows = BinaryMatrix.decode 248 aBaseRows :=
  checked_mul 248 aInverseRows aLeftRows aBaseRows (by decide) aBase_check

end Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates
