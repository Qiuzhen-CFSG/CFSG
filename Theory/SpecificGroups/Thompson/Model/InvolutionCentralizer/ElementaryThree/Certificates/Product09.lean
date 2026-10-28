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

private theorem rawInv_check00 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 0 16 = true := by
  decide +kernel

private theorem rawInv_check01 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 16 16 = true := by
  decide +kernel

private theorem rawInv_check02 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 32 16 = true := by
  decide +kernel

private theorem rawInv_check03 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 48 16 = true := by
  decide +kernel

private theorem rawInv_check04 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 64 16 = true := by
  decide +kernel

private theorem rawInv_check05 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 80 16 = true := by
  decide +kernel

private theorem rawInv_check06 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 96 16 = true := by
  decide +kernel

private theorem rawInv_check07 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 112 16 = true := by
  decide +kernel

private theorem rawInv_check08 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 128 16 = true := by
  decide +kernel

private theorem rawInv_check09 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 144 16 = true := by
  decide +kernel

private theorem rawInv_check10 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 160 16 = true := by
  decide +kernel

private theorem rawInv_check11 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 176 16 = true := by
  decide +kernel

private theorem rawInv_check12 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 192 16 = true := by
  decide +kernel

private theorem rawInv_check13 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 208 16 = true := by
  decide +kernel

private theorem rawInv_check14 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 224 16 = true := by
  decide +kernel

private theorem rawInv_check15 :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 240 8 = true := by
  decide +kernel

private theorem rawInv_check :
    checkRange (fun i => BinaryMatrix.listProduct rawXYRows[i]! xyInvRows.toList 0 == rawInvRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) rawInv_check00
      (checkRange_append (m := 16) (n := 216) rawInv_check01
      (checkRange_append (m := 16) (n := 200) rawInv_check02
      (checkRange_append (m := 16) (n := 184) rawInv_check03
      (checkRange_append (m := 16) (n := 168) rawInv_check04
      (checkRange_append (m := 16) (n := 152) rawInv_check05
      (checkRange_append (m := 16) (n := 136) rawInv_check06
      (checkRange_append (m := 16) (n := 120) rawInv_check07
      (checkRange_append (m := 16) (n := 104) rawInv_check08
      (checkRange_append (m := 16) (n := 88) rawInv_check09
      (checkRange_append (m := 16) (n := 72) rawInv_check10
      (checkRange_append (m := 16) (n := 56) rawInv_check11
      (checkRange_append (m := 16) (n := 40) rawInv_check12
      (checkRange_append (m := 16) (n := 24) rawInv_check13
      (checkRange_append (m := 16) (n := 8) rawInv_check14
      rawInv_check15)))))))))))))))

/-- Kernel-checked matrix product for `rawInv`. -/
theorem rawInv_product : BinaryMatrix.decode 248 rawXYRows *
    BinaryMatrix.decode 248 xyInvRows = BinaryMatrix.decode 248 rawInvRows :=
  checked_mul 248 rawXYRows xyInvRows rawInvRows (by decide) rawInv_check

end Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
