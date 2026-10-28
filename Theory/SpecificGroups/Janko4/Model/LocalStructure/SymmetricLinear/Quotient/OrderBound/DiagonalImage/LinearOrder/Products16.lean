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
theorem product_147_0 :
    decodeRows rows147 * decodeRows linearFirstRows = decodeRows rows163 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_150_1 :
    decodeRows rows150 * decodeRows linearSecondRows = decodeRows rows164 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_151_1 :
    decodeRows rows151 * decodeRows linearSecondRows = decodeRows rows163 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_152_0 :
    decodeRows rows152 * decodeRows linearFirstRows = decodeRows rows165 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_153_1 :
    decodeRows rows153 * decodeRows linearSecondRows = decodeRows rows151 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_154_0 :
    decodeRows rows154 * decodeRows linearFirstRows = decodeRows rows159 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_154_1 :
    decodeRows rows154 * decodeRows linearSecondRows = decodeRows rows166 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_156_0 :
    decodeRows rows156 * decodeRows linearFirstRows = decodeRows rows167 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_156_1 :
    decodeRows rows156 * decodeRows linearSecondRows = decodeRows rows138 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_157_0 :
    decodeRows rows157 * decodeRows linearFirstRows = decodeRows rows166 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_157_1 :
    decodeRows rows157 * decodeRows linearSecondRows = decodeRows rows149 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_159_1 :
    decodeRows rows159 * decodeRows linearSecondRows = decodeRows rows165 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.LinearEnumeration
