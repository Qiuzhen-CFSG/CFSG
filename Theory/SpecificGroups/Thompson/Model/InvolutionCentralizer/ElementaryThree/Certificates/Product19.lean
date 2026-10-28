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

private theorem conj1Prefix_check00 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 0 16 = true := by
  decide +kernel

private theorem conj1Prefix_check01 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 16 16 = true := by
  decide +kernel

private theorem conj1Prefix_check02 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 32 16 = true := by
  decide +kernel

private theorem conj1Prefix_check03 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 48 16 = true := by
  decide +kernel

private theorem conj1Prefix_check04 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 64 16 = true := by
  decide +kernel

private theorem conj1Prefix_check05 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 80 16 = true := by
  decide +kernel

private theorem conj1Prefix_check06 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 96 16 = true := by
  decide +kernel

private theorem conj1Prefix_check07 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 112 16 = true := by
  decide +kernel

private theorem conj1Prefix_check08 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 128 16 = true := by
  decide +kernel

private theorem conj1Prefix_check09 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 144 16 = true := by
  decide +kernel

private theorem conj1Prefix_check10 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 160 16 = true := by
  decide +kernel

private theorem conj1Prefix_check11 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 176 16 = true := by
  decide +kernel

private theorem conj1Prefix_check12 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 192 16 = true := by
  decide +kernel

private theorem conj1Prefix_check13 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 208 16 = true := by
  decide +kernel

private theorem conj1Prefix_check14 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 224 16 = true := by
  decide +kernel

private theorem conj1Prefix_check15 :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 240 8 = true := by
  decide +kernel

private theorem conj1Prefix_check :
    checkRange (fun i => BinaryMatrix.listProduct yxRows[i]! y4Rows.toList 0 == conj1PrefixRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) conj1Prefix_check00
      (checkRange_append (m := 16) (n := 216) conj1Prefix_check01
      (checkRange_append (m := 16) (n := 200) conj1Prefix_check02
      (checkRange_append (m := 16) (n := 184) conj1Prefix_check03
      (checkRange_append (m := 16) (n := 168) conj1Prefix_check04
      (checkRange_append (m := 16) (n := 152) conj1Prefix_check05
      (checkRange_append (m := 16) (n := 136) conj1Prefix_check06
      (checkRange_append (m := 16) (n := 120) conj1Prefix_check07
      (checkRange_append (m := 16) (n := 104) conj1Prefix_check08
      (checkRange_append (m := 16) (n := 88) conj1Prefix_check09
      (checkRange_append (m := 16) (n := 72) conj1Prefix_check10
      (checkRange_append (m := 16) (n := 56) conj1Prefix_check11
      (checkRange_append (m := 16) (n := 40) conj1Prefix_check12
      (checkRange_append (m := 16) (n := 24) conj1Prefix_check13
      (checkRange_append (m := 16) (n := 8) conj1Prefix_check14
      conj1Prefix_check15)))))))))))))))

/-- Kernel-checked matrix product for `conj1Prefix`. -/
theorem conj1Prefix_product : BinaryMatrix.decode 248 yxRows *
    BinaryMatrix.decode 248 y4Rows = BinaryMatrix.decode 248 conj1PrefixRows :=
  checked_mul 248 yxRows y4Rows conj1PrefixRows (by decide) conj1Prefix_check

end Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
