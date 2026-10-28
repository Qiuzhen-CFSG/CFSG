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

private theorem xy_check00 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 0 16 = true := by
  decide +kernel

private theorem xy_check01 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 16 16 = true := by
  decide +kernel

private theorem xy_check02 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 32 16 = true := by
  decide +kernel

private theorem xy_check03 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 48 16 = true := by
  decide +kernel

private theorem xy_check04 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 64 16 = true := by
  decide +kernel

private theorem xy_check05 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 80 16 = true := by
  decide +kernel

private theorem xy_check06 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 96 16 = true := by
  decide +kernel

private theorem xy_check07 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 112 16 = true := by
  decide +kernel

private theorem xy_check08 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 128 16 = true := by
  decide +kernel

private theorem xy_check09 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 144 16 = true := by
  decide +kernel

private theorem xy_check10 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 160 16 = true := by
  decide +kernel

private theorem xy_check11 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 176 16 = true := by
  decide +kernel

private theorem xy_check12 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 192 16 = true := by
  decide +kernel

private theorem xy_check13 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 208 16 = true := by
  decide +kernel

private theorem xy_check14 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 224 16 = true := by
  decide +kernel

private theorem xy_check15 :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 240 8 = true := by
  decide +kernel

private theorem xy_check :
    checkRange (fun i => BinaryMatrix.listProduct AlternatingQuotient.wordARows[i]! AlternatingQuotient.wordBRows.toList 0 == xyRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) xy_check00
      (checkRange_append (m := 16) (n := 216) xy_check01
      (checkRange_append (m := 16) (n := 200) xy_check02
      (checkRange_append (m := 16) (n := 184) xy_check03
      (checkRange_append (m := 16) (n := 168) xy_check04
      (checkRange_append (m := 16) (n := 152) xy_check05
      (checkRange_append (m := 16) (n := 136) xy_check06
      (checkRange_append (m := 16) (n := 120) xy_check07
      (checkRange_append (m := 16) (n := 104) xy_check08
      (checkRange_append (m := 16) (n := 88) xy_check09
      (checkRange_append (m := 16) (n := 72) xy_check10
      (checkRange_append (m := 16) (n := 56) xy_check11
      (checkRange_append (m := 16) (n := 40) xy_check12
      (checkRange_append (m := 16) (n := 24) xy_check13
      (checkRange_append (m := 16) (n := 8) xy_check14
      xy_check15)))))))))))))))

/-- Kernel-checked matrix product for `xy`. -/
theorem xy_product : BinaryMatrix.decode 248 AlternatingQuotient.wordARows *
    BinaryMatrix.decode 248 AlternatingQuotient.wordBRows = BinaryMatrix.decode 248 xyRows :=
  checked_mul 248 AlternatingQuotient.wordARows AlternatingQuotient.wordBRows xyRows (by decide) xy_check

end Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
