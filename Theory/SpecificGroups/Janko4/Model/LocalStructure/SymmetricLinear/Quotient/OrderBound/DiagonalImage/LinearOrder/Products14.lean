module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Data

/-!
# Full-matrix transition products

Every displayed product is checked on all 112 packed rows using Lean kernel
reduction and decode_packedMul. Generated from the untrusted enumeration;
source attribution and reproduction are in LinearOrder/source/README.md.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.LinearEnumeration

open GeneratorCertificates Simplicity.Elevens.BridgeCertificate

set_option maxRecDepth 10000 in
theorem product_123_1 :
    decodeRows rows123 * decodeRows linearSecondRows = decodeRows rows148 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_124_1 :
    decodeRows rows124 * decodeRows linearSecondRows = decodeRows rows114 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_125_0 :
    decodeRows rows125 * decodeRows linearFirstRows = decodeRows rows149 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_126_0 :
    decodeRows rows126 * decodeRows linearFirstRows = decodeRows rows150 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_126_1 :
    decodeRows rows126 * decodeRows linearSecondRows = decodeRows rows124 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_128_0 :
    decodeRows rows128 * decodeRows linearFirstRows = decodeRows rows151 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_128_1 :
    decodeRows rows128 * decodeRows linearSecondRows = decodeRows rows152 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_129_1 :
    decodeRows rows129 * decodeRows linearSecondRows = decodeRows rows153 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_130_1 :
    decodeRows rows130 * decodeRows linearSecondRows = decodeRows rows154 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_131_0 :
    decodeRows rows131 * decodeRows linearFirstRows = decodeRows rows155 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_132_1 :
    decodeRows rows132 * decodeRows linearSecondRows = decodeRows rows156 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_133_1 :
    decodeRows rows133 * decodeRows linearSecondRows = decodeRows rows087 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.LinearEnumeration
