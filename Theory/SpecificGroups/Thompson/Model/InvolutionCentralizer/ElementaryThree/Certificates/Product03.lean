module

public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates.PackedRows
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates.Checker

/-!
# Binary certificates for the fixed Thompson cubic words

Packed rows use the original ATLAS matrix multiplication convention. Every
product is checked in small row intervals by the Lean kernel. Inverse witnesses
are checked by multiplication to the identity; group inverse uniqueness links
them to the actual words in the assembly module.

Source: ATLAS `ThG1-f2r248B0` and `ThG1-max3W1`, GLS3 Table 5.3x,
and Aschbacher--Smith A.2.19 and I.1.3. See `../source/README.md` for
attribution, reproduction and measured compilation costs.
-/

public section
namespace Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
open AlternatingQuotient.MatrixCertificates

-- Keep the measured sixteen-row reductions sequential within each certificate.
set_option Elab.async false
set_option maxRecDepth 2048

private theorem xyInv2_check00 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 0 16 = true := by
  decide +kernel

private theorem xyInv2_check01 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 16 16 = true := by
  decide +kernel

private theorem xyInv2_check02 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 32 16 = true := by
  decide +kernel

private theorem xyInv2_check03 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 48 16 = true := by
  decide +kernel

private theorem xyInv2_check04 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 64 16 = true := by
  decide +kernel

private theorem xyInv2_check05 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 80 16 = true := by
  decide +kernel

private theorem xyInv2_check06 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 96 16 = true := by
  decide +kernel

private theorem xyInv2_check07 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 112 16 = true := by
  decide +kernel

private theorem xyInv2_check08 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 128 16 = true := by
  decide +kernel

private theorem xyInv2_check09 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 144 16 = true := by
  decide +kernel

private theorem xyInv2_check10 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 160 16 = true := by
  decide +kernel

private theorem xyInv2_check11 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 176 16 = true := by
  decide +kernel

private theorem xyInv2_check12 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 192 16 = true := by
  decide +kernel

private theorem xyInv2_check13 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 208 16 = true := by
  decide +kernel

private theorem xyInv2_check14 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 224 16 = true := by
  decide +kernel

private theorem xyInv2_check15 :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 240 8 = true := by
  decide +kernel

private theorem xyInv2_check :
    checkRange (fun i => BinaryMatrix.listProduct xyInvRows[i]! xyInvRows.toList 0 == xyInv2Rows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) xyInv2_check00
      (checkRange_append (m := 16) (n := 216) xyInv2_check01
      (checkRange_append (m := 16) (n := 200) xyInv2_check02
      (checkRange_append (m := 16) (n := 184) xyInv2_check03
      (checkRange_append (m := 16) (n := 168) xyInv2_check04
      (checkRange_append (m := 16) (n := 152) xyInv2_check05
      (checkRange_append (m := 16) (n := 136) xyInv2_check06
      (checkRange_append (m := 16) (n := 120) xyInv2_check07
      (checkRange_append (m := 16) (n := 104) xyInv2_check08
      (checkRange_append (m := 16) (n := 88) xyInv2_check09
      (checkRange_append (m := 16) (n := 72) xyInv2_check10
      (checkRange_append (m := 16) (n := 56) xyInv2_check11
      (checkRange_append (m := 16) (n := 40) xyInv2_check12
      (checkRange_append (m := 16) (n := 24) xyInv2_check13
      (checkRange_append (m := 16) (n := 8) xyInv2_check14
      xyInv2_check15)))))))))))))))

/-- Kernel-checked matrix product for `xyInv2`. -/
theorem xyInv2_product : BinaryMatrix.decode 248 xyInvRows *
    BinaryMatrix.decode 248 xyInvRows = BinaryMatrix.decode 248 xyInv2Rows :=
  checked_mul 248 xyInvRows xyInvRows xyInv2Rows (by decide) xyInv2_check

end Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
