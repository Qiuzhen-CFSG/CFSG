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

private theorem y2_check00 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 0 16 = true := by
  decide +kernel

private theorem y2_check01 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 16 16 = true := by
  decide +kernel

private theorem y2_check02 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 32 16 = true := by
  decide +kernel

private theorem y2_check03 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 48 16 = true := by
  decide +kernel

private theorem y2_check04 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 64 16 = true := by
  decide +kernel

private theorem y2_check05 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 80 16 = true := by
  decide +kernel

private theorem y2_check06 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 96 16 = true := by
  decide +kernel

private theorem y2_check07 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 112 16 = true := by
  decide +kernel

private theorem y2_check08 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 128 16 = true := by
  decide +kernel

private theorem y2_check09 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 144 16 = true := by
  decide +kernel

private theorem y2_check10 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 160 16 = true := by
  decide +kernel

private theorem y2_check11 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 176 16 = true := by
  decide +kernel

private theorem y2_check12 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 192 16 = true := by
  decide +kernel

private theorem y2_check13 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 208 16 = true := by
  decide +kernel

private theorem y2_check14 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 224 16 = true := by
  decide +kernel

private theorem y2_check15 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 240 8 = true := by
  decide +kernel

private theorem y2_check :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordBRows[i]! AlternatingQuotient.wordBRows.toList 0 == y2Rows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) y2_check00
      (checkRange_append (m := 16) (n := 216) y2_check01
      (checkRange_append (m := 16) (n := 200) y2_check02
      (checkRange_append (m := 16) (n := 184) y2_check03
      (checkRange_append (m := 16) (n := 168) y2_check04
      (checkRange_append (m := 16) (n := 152) y2_check05
      (checkRange_append (m := 16) (n := 136) y2_check06
      (checkRange_append (m := 16) (n := 120) y2_check07
      (checkRange_append (m := 16) (n := 104) y2_check08
      (checkRange_append (m := 16) (n := 88) y2_check09
      (checkRange_append (m := 16) (n := 72) y2_check10
      (checkRange_append (m := 16) (n := 56) y2_check11
      (checkRange_append (m := 16) (n := 40) y2_check12
      (checkRange_append (m := 16) (n := 24) y2_check13
      (checkRange_append (m := 16) (n := 8) y2_check14
      y2_check15)))))))))))))))

/-- Kernel-checked matrix product for `y2`. -/
theorem y2_product : BinaryMatrix.decode 248 AlternatingQuotient.wordBRows *
    BinaryMatrix.decode 248 AlternatingQuotient.wordBRows = BinaryMatrix.decode 248 y2Rows :=
  checked_mul 248 AlternatingQuotient.wordBRows AlternatingQuotient.wordBRows y2Rows (by decide) y2_check

end Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
