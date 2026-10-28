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

private theorem y3_check00 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 0 16 = true := by
  decide +kernel

private theorem y3_check01 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 16 16 = true := by
  decide +kernel

private theorem y3_check02 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 32 16 = true := by
  decide +kernel

private theorem y3_check03 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 48 16 = true := by
  decide +kernel

private theorem y3_check04 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 64 16 = true := by
  decide +kernel

private theorem y3_check05 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 80 16 = true := by
  decide +kernel

private theorem y3_check06 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 96 16 = true := by
  decide +kernel

private theorem y3_check07 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 112 16 = true := by
  decide +kernel

private theorem y3_check08 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 128 16 = true := by
  decide +kernel

private theorem y3_check09 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 144 16 = true := by
  decide +kernel

private theorem y3_check10 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 160 16 = true := by
  decide +kernel

private theorem y3_check11 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 176 16 = true := by
  decide +kernel

private theorem y3_check12 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 192 16 = true := by
  decide +kernel

private theorem y3_check13 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 208 16 = true := by
  decide +kernel

private theorem y3_check14 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 224 16 = true := by
  decide +kernel

private theorem y3_check15 :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 240 8 = true := by
  decide +kernel

private theorem y3_check :
    checkRange (fun i => BinaryMatrix.listProduct y2Rows[i]! AlternatingQuotient.wordBRows.toList 0 == y3Rows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) y3_check00
      (checkRange_append (m := 16) (n := 216) y3_check01
      (checkRange_append (m := 16) (n := 200) y3_check02
      (checkRange_append (m := 16) (n := 184) y3_check03
      (checkRange_append (m := 16) (n := 168) y3_check04
      (checkRange_append (m := 16) (n := 152) y3_check05
      (checkRange_append (m := 16) (n := 136) y3_check06
      (checkRange_append (m := 16) (n := 120) y3_check07
      (checkRange_append (m := 16) (n := 104) y3_check08
      (checkRange_append (m := 16) (n := 88) y3_check09
      (checkRange_append (m := 16) (n := 72) y3_check10
      (checkRange_append (m := 16) (n := 56) y3_check11
      (checkRange_append (m := 16) (n := 40) y3_check12
      (checkRange_append (m := 16) (n := 24) y3_check13
      (checkRange_append (m := 16) (n := 8) y3_check14
      y3_check15)))))))))))))))

/-- Kernel-checked matrix product for `y3`. -/
theorem y3_product : BinaryMatrix.decode 248 y2Rows *
    BinaryMatrix.decode 248 AlternatingQuotient.wordBRows = BinaryMatrix.decode 248 y3Rows :=
  checked_mul 248 y2Rows AlternatingQuotient.wordBRows y3Rows (by decide) y3_check

end Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
