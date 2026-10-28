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
theorem product_134_1 :
    decodeRows rows134 * decodeRows linearSecondRows = decodeRows rows157 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_136_0 :
    decodeRows rows136 * decodeRows linearFirstRows = decodeRows rows158 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_136_1 :
    decodeRows rows136 * decodeRows linearSecondRows = decodeRows rows122 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_137_0 :
    decodeRows rows137 * decodeRows linearFirstRows = decodeRows rows148 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_139_1 :
    decodeRows rows139 * decodeRows linearSecondRows = decodeRows rows159 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_140_1 :
    decodeRows rows140 * decodeRows linearSecondRows = decodeRows rows158 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_141_0 :
    decodeRows rows141 * decodeRows linearFirstRows = decodeRows rows160 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_142_0 :
    decodeRows rows142 * decodeRows linearFirstRows = decodeRows rows153 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_142_1 :
    decodeRows rows142 * decodeRows linearSecondRows = decodeRows rows140 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_143_1 :
    decodeRows rows143 * decodeRows linearSecondRows = decodeRows rows161 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_144_0 :
    decodeRows rows144 * decodeRows linearFirstRows = decodeRows rows162 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_145_1 :
    decodeRows rows145 * decodeRows linearSecondRows = decodeRows rows099 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.LinearEnumeration
