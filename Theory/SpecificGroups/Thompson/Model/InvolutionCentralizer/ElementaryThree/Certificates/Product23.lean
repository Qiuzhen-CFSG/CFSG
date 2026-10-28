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

private theorem conj2Y_check00 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 0 16 = true := by
  decide +kernel

private theorem conj2Y_check01 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 16 16 = true := by
  decide +kernel

private theorem conj2Y_check02 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 32 16 = true := by
  decide +kernel

private theorem conj2Y_check03 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 48 16 = true := by
  decide +kernel

private theorem conj2Y_check04 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 64 16 = true := by
  decide +kernel

private theorem conj2Y_check05 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 80 16 = true := by
  decide +kernel

private theorem conj2Y_check06 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 96 16 = true := by
  decide +kernel

private theorem conj2Y_check07 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 112 16 = true := by
  decide +kernel

private theorem conj2Y_check08 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 128 16 = true := by
  decide +kernel

private theorem conj2Y_check09 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 144 16 = true := by
  decide +kernel

private theorem conj2Y_check10 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 160 16 = true := by
  decide +kernel

private theorem conj2Y_check11 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 176 16 = true := by
  decide +kernel

private theorem conj2Y_check12 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 192 16 = true := by
  decide +kernel

private theorem conj2Y_check13 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 208 16 = true := by
  decide +kernel

private theorem conj2Y_check14 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 224 16 = true := by
  decide +kernel

private theorem conj2Y_check15 :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 240 8 = true := by
  decide +kernel

private theorem conj2Y_check :
    checkRange (fun i => BinaryMatrix.listProduct conj2MiddleRows[i]! y3Rows.toList 0 == conj2YRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) conj2Y_check00
      (checkRange_append (m := 16) (n := 216) conj2Y_check01
      (checkRange_append (m := 16) (n := 200) conj2Y_check02
      (checkRange_append (m := 16) (n := 184) conj2Y_check03
      (checkRange_append (m := 16) (n := 168) conj2Y_check04
      (checkRange_append (m := 16) (n := 152) conj2Y_check05
      (checkRange_append (m := 16) (n := 136) conj2Y_check06
      (checkRange_append (m := 16) (n := 120) conj2Y_check07
      (checkRange_append (m := 16) (n := 104) conj2Y_check08
      (checkRange_append (m := 16) (n := 88) conj2Y_check09
      (checkRange_append (m := 16) (n := 72) conj2Y_check10
      (checkRange_append (m := 16) (n := 56) conj2Y_check11
      (checkRange_append (m := 16) (n := 40) conj2Y_check12
      (checkRange_append (m := 16) (n := 24) conj2Y_check13
      (checkRange_append (m := 16) (n := 8) conj2Y_check14
      conj2Y_check15)))))))))))))))

/-- Kernel-checked matrix product for `conj2Y`. -/
theorem conj2Y_product : BinaryMatrix.decode 248 conj2MiddleRows *
    BinaryMatrix.decode 248 y3Rows = BinaryMatrix.decode 248 conj2YRows :=
  checked_mul 248 conj2MiddleRows y3Rows conj2YRows (by decide) conj2Y_check

end Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
