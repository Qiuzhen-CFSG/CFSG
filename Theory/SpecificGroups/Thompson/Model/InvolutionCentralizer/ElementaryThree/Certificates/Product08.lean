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

private theorem rawXY_check00 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 0 16 = true := by
  decide +kernel

private theorem rawXY_check01 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 16 16 = true := by
  decide +kernel

private theorem rawXY_check02 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 32 16 = true := by
  decide +kernel

private theorem rawXY_check03 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 48 16 = true := by
  decide +kernel

private theorem rawXY_check04 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 64 16 = true := by
  decide +kernel

private theorem rawXY_check05 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 80 16 = true := by
  decide +kernel

private theorem rawXY_check06 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 96 16 = true := by
  decide +kernel

private theorem rawXY_check07 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 112 16 = true := by
  decide +kernel

private theorem rawXY_check08 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 128 16 = true := by
  decide +kernel

private theorem rawXY_check09 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 144 16 = true := by
  decide +kernel

private theorem rawXY_check10 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 160 16 = true := by
  decide +kernel

private theorem rawXY_check11 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 176 16 = true := by
  decide +kernel

private theorem rawXY_check12 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 192 16 = true := by
  decide +kernel

private theorem rawXY_check13 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 208 16 = true := by
  decide +kernel

private theorem rawXY_check14 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 224 16 = true := by
  decide +kernel

private theorem rawXY_check15 :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 240 8 = true := by
  decide +kernel

private theorem rawXY_check :
    checkRange (fun i => BinaryMatrix.listProduct rawYRows[i]! xyRows.toList 0 == rawXYRows[i]!) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) rawXY_check00
      (checkRange_append (m := 16) (n := 216) rawXY_check01
      (checkRange_append (m := 16) (n := 200) rawXY_check02
      (checkRange_append (m := 16) (n := 184) rawXY_check03
      (checkRange_append (m := 16) (n := 168) rawXY_check04
      (checkRange_append (m := 16) (n := 152) rawXY_check05
      (checkRange_append (m := 16) (n := 136) rawXY_check06
      (checkRange_append (m := 16) (n := 120) rawXY_check07
      (checkRange_append (m := 16) (n := 104) rawXY_check08
      (checkRange_append (m := 16) (n := 88) rawXY_check09
      (checkRange_append (m := 16) (n := 72) rawXY_check10
      (checkRange_append (m := 16) (n := 56) rawXY_check11
      (checkRange_append (m := 16) (n := 40) rawXY_check12
      (checkRange_append (m := 16) (n := 24) rawXY_check13
      (checkRange_append (m := 16) (n := 8) rawXY_check14
      rawXY_check15)))))))))))))))

/-- Kernel-checked matrix product for `rawXY`. -/
theorem rawXY_product : BinaryMatrix.decode 248 rawYRows *
    BinaryMatrix.decode 248 xyRows = BinaryMatrix.decode 248 rawXYRows :=
  checked_mul 248 rawYRows xyRows rawXYRows (by decide) rawXY_check

end Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
