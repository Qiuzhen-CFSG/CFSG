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

private theorem triple2_check00 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 0 16 = true := by
  decide +kernel

private theorem triple2_check01 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 16 16 = true := by
  decide +kernel

private theorem triple2_check02 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 32 16 = true := by
  decide +kernel

private theorem triple2_check03 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 48 16 = true := by
  decide +kernel

private theorem triple2_check04 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 64 16 = true := by
  decide +kernel

private theorem triple2_check05 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 80 16 = true := by
  decide +kernel

private theorem triple2_check06 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 96 16 = true := by
  decide +kernel

private theorem triple2_check07 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 112 16 = true := by
  decide +kernel

private theorem triple2_check08 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 128 16 = true := by
  decide +kernel

private theorem triple2_check09 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 144 16 = true := by
  decide +kernel

private theorem triple2_check10 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 160 16 = true := by
  decide +kernel

private theorem triple2_check11 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 176 16 = true := by
  decide +kernel

private theorem triple2_check12 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 192 16 = true := by
  decide +kernel

private theorem triple2_check13 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 208 16 = true := by
  decide +kernel

private theorem triple2_check14 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 224 16 = true := by
  decide +kernel

private theorem triple2_check15 :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 240 8 = true := by
  decide +kernel

private theorem triple2_check :
    checkRange (fun i => BinaryMatrix.listProduct triple2PrefixRows[i]! conj2Rows.toList 0 == triple2Rows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) triple2_check00
      (checkRange_append (m := 16) (n := 216) triple2_check01
      (checkRange_append (m := 16) (n := 200) triple2_check02
      (checkRange_append (m := 16) (n := 184) triple2_check03
      (checkRange_append (m := 16) (n := 168) triple2_check04
      (checkRange_append (m := 16) (n := 152) triple2_check05
      (checkRange_append (m := 16) (n := 136) triple2_check06
      (checkRange_append (m := 16) (n := 120) triple2_check07
      (checkRange_append (m := 16) (n := 104) triple2_check08
      (checkRange_append (m := 16) (n := 88) triple2_check09
      (checkRange_append (m := 16) (n := 72) triple2_check10
      (checkRange_append (m := 16) (n := 56) triple2_check11
      (checkRange_append (m := 16) (n := 40) triple2_check12
      (checkRange_append (m := 16) (n := 24) triple2_check13
      (checkRange_append (m := 16) (n := 8) triple2_check14
      triple2_check15)))))))))))))))

/-- Kernel-checked matrix product for `triple2`. -/
theorem triple2_product : BinaryMatrix.decode 248 triple2PrefixRows *
    BinaryMatrix.decode 248 conj2Rows = BinaryMatrix.decode 248 triple2Rows :=
  checked_mul 248 triple2PrefixRows conj2Rows triple2Rows (by decide) triple2_check

end Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
