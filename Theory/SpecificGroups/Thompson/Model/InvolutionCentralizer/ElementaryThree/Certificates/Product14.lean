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

private theorem base_cube_check00 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 0 16 = true := by
  decide +kernel

private theorem base_cube_check01 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 16 16 = true := by
  decide +kernel

private theorem base_cube_check02 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 32 16 = true := by
  decide +kernel

private theorem base_cube_check03 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 48 16 = true := by
  decide +kernel

private theorem base_cube_check04 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 64 16 = true := by
  decide +kernel

private theorem base_cube_check05 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 80 16 = true := by
  decide +kernel

private theorem base_cube_check06 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 96 16 = true := by
  decide +kernel

private theorem base_cube_check07 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 112 16 = true := by
  decide +kernel

private theorem base_cube_check08 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 128 16 = true := by
  decide +kernel

private theorem base_cube_check09 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 144 16 = true := by
  decide +kernel

private theorem base_cube_check10 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 160 16 = true := by
  decide +kernel

private theorem base_cube_check11 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 176 16 = true := by
  decide +kernel

private theorem base_cube_check12 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 192 16 = true := by
  decide +kernel

private theorem base_cube_check13 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 208 16 = true := by
  decide +kernel

private theorem base_cube_check14 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 224 16 = true := by
  decide +kernel

private theorem base_cube_check15 :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 240 8 = true := by
  decide +kernel

private theorem base_cube_check :
    checkRange (fun i => BinaryMatrix.listProduct base2Rows[i]! baseRows.toList 0 == 2 ^ i) 0 248 = true :=
  (checkRange_append (m := 16) (n := 232) base_cube_check00
      (checkRange_append (m := 16) (n := 216) base_cube_check01
      (checkRange_append (m := 16) (n := 200) base_cube_check02
      (checkRange_append (m := 16) (n := 184) base_cube_check03
      (checkRange_append (m := 16) (n := 168) base_cube_check04
      (checkRange_append (m := 16) (n := 152) base_cube_check05
      (checkRange_append (m := 16) (n := 136) base_cube_check06
      (checkRange_append (m := 16) (n := 120) base_cube_check07
      (checkRange_append (m := 16) (n := 104) base_cube_check08
      (checkRange_append (m := 16) (n := 88) base_cube_check09
      (checkRange_append (m := 16) (n := 72) base_cube_check10
      (checkRange_append (m := 16) (n := 56) base_cube_check11
      (checkRange_append (m := 16) (n := 40) base_cube_check12
      (checkRange_append (m := 16) (n := 24) base_cube_check13
      (checkRange_append (m := 16) (n := 8) base_cube_check14
      base_cube_check15)))))))))))))))

/-- Kernel-checked matrix product for `base_cube`. -/
theorem base_cube_product : BinaryMatrix.decode 248 base2Rows *
    BinaryMatrix.decode 248 baseRows = 1 :=
  checked_mul_one 248 base2Rows baseRows (by decide) base_cube_check

end Thompson.InvolutionCentralizer.ElementaryThree.CertificateData
