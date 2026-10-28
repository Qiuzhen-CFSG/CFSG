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

private theorem rawPrefix_check00 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 0 16 = true := by
  decide +kernel

private theorem rawPrefix_check01 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 16 16 = true := by
  decide +kernel

private theorem rawPrefix_check02 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 32 16 = true := by
  decide +kernel

private theorem rawPrefix_check03 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 48 16 = true := by
  decide +kernel

private theorem rawPrefix_check04 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 64 16 = true := by
  decide +kernel

private theorem rawPrefix_check05 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 80 16 = true := by
  decide +kernel

private theorem rawPrefix_check06 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 96 16 = true := by
  decide +kernel

private theorem rawPrefix_check07 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 112 16 = true := by
  decide +kernel

private theorem rawPrefix_check08 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 128 16 = true := by
  decide +kernel

private theorem rawPrefix_check09 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 144 16 = true := by
  decide +kernel

private theorem rawPrefix_check10 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 160 16 = true := by
  decide +kernel

private theorem rawPrefix_check11 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 176 16 = true := by
  decide +kernel

private theorem rawPrefix_check12 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 192 16 = true := by
  decide +kernel

private theorem rawPrefix_check13 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 208 16 = true := by
  decide +kernel

private theorem rawPrefix_check14 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 224 16 = true := by
  decide +kernel

private theorem rawPrefix_check15 :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 240 8 = true := by
  decide +kernel

private theorem rawPrefix_check :
    checkRange (fun i => BinaryMatrix.listProduct xyInv2Rows[i]! xy3Rows.toList 0 == rawPrefixRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) rawPrefix_check00
      (checkRange_append (m := 16) (n := 216) rawPrefix_check01
      (checkRange_append (m := 16) (n := 200) rawPrefix_check02
      (checkRange_append (m := 16) (n := 184) rawPrefix_check03
      (checkRange_append (m := 16) (n := 168) rawPrefix_check04
      (checkRange_append (m := 16) (n := 152) rawPrefix_check05
      (checkRange_append (m := 16) (n := 136) rawPrefix_check06
      (checkRange_append (m := 16) (n := 120) rawPrefix_check07
      (checkRange_append (m := 16) (n := 104) rawPrefix_check08
      (checkRange_append (m := 16) (n := 88) rawPrefix_check09
      (checkRange_append (m := 16) (n := 72) rawPrefix_check10
      (checkRange_append (m := 16) (n := 56) rawPrefix_check11
      (checkRange_append (m := 16) (n := 40) rawPrefix_check12
      (checkRange_append (m := 16) (n := 24) rawPrefix_check13
      (checkRange_append (m := 16) (n := 8) rawPrefix_check14
      rawPrefix_check15)))))))))))))))

/-- Kernel-checked matrix product for `rawPrefix`. -/
theorem rawPrefix_product : BinaryMatrix.decode 248 xyInv2Rows *
    BinaryMatrix.decode 248 xy3Rows = BinaryMatrix.decode 248 rawPrefixRows :=
  checked_mul 248 xyInv2Rows xy3Rows rawPrefixRows (by decide) rawPrefix_check

end Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
