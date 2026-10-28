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

private theorem commute21_check00 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 0 16 = true := by
  decide +kernel

private theorem commute21_check01 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 16 16 = true := by
  decide +kernel

private theorem commute21_check02 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 32 16 = true := by
  decide +kernel

private theorem commute21_check03 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 48 16 = true := by
  decide +kernel

private theorem commute21_check04 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 64 16 = true := by
  decide +kernel

private theorem commute21_check05 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 80 16 = true := by
  decide +kernel

private theorem commute21_check06 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 96 16 = true := by
  decide +kernel

private theorem commute21_check07 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 112 16 = true := by
  decide +kernel

private theorem commute21_check08 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 128 16 = true := by
  decide +kernel

private theorem commute21_check09 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 144 16 = true := by
  decide +kernel

private theorem commute21_check10 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 160 16 = true := by
  decide +kernel

private theorem commute21_check11 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 176 16 = true := by
  decide +kernel

private theorem commute21_check12 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 192 16 = true := by
  decide +kernel

private theorem commute21_check13 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 208 16 = true := by
  decide +kernel

private theorem commute21_check14 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 224 16 = true := by
  decide +kernel

private theorem commute21_check15 :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 240 8 = true := by
  decide +kernel

private theorem commute21_check :
    checkRange (fun i => BinaryMatrix.listProduct triple2Rows[i]! triple1Rows.toList 0 == commute12Rows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) commute21_check00
      (checkRange_append (m := 16) (n := 216) commute21_check01
      (checkRange_append (m := 16) (n := 200) commute21_check02
      (checkRange_append (m := 16) (n := 184) commute21_check03
      (checkRange_append (m := 16) (n := 168) commute21_check04
      (checkRange_append (m := 16) (n := 152) commute21_check05
      (checkRange_append (m := 16) (n := 136) commute21_check06
      (checkRange_append (m := 16) (n := 120) commute21_check07
      (checkRange_append (m := 16) (n := 104) commute21_check08
      (checkRange_append (m := 16) (n := 88) commute21_check09
      (checkRange_append (m := 16) (n := 72) commute21_check10
      (checkRange_append (m := 16) (n := 56) commute21_check11
      (checkRange_append (m := 16) (n := 40) commute21_check12
      (checkRange_append (m := 16) (n := 24) commute21_check13
      (checkRange_append (m := 16) (n := 8) commute21_check14
      commute21_check15)))))))))))))))

/-- Kernel-checked matrix product for `commute21`. -/
theorem commute21_product : BinaryMatrix.decode 248 triple2Rows *
    BinaryMatrix.decode 248 triple1Rows = BinaryMatrix.decode 248 commute12Rows :=
  checked_mul 248 triple2Rows triple1Rows commute12Rows (by decide) commute21_check

end Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
