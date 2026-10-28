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
theorem product_068_1 :
    decodeRows rows068 * decodeRows linearSecondRows = decodeRows rows090 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_069_0 :
    decodeRows rows069 * decodeRows linearFirstRows = decodeRows rows085 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_069_1 :
    decodeRows rows069 * decodeRows linearSecondRows = decodeRows rows091 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_071_0 :
    decodeRows rows071 * decodeRows linearFirstRows = decodeRows rows092 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_071_1 :
    decodeRows rows071 * decodeRows linearSecondRows = decodeRows rows093 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_072_0 :
    decodeRows rows072 * decodeRows linearFirstRows = decodeRows rows094 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_073_1 :
    decodeRows rows073 * decodeRows linearSecondRows = decodeRows rows095 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_074_0 :
    decodeRows rows074 * decodeRows linearFirstRows = decodeRows rows096 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_074_1 :
    decodeRows rows074 * decodeRows linearSecondRows = decodeRows rows097 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_075_1 :
    decodeRows rows075 * decodeRows linearSecondRows = decodeRows rows098 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_076_0 :
    decodeRows rows076 * decodeRows linearFirstRows = decodeRows rows099 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_076_1 :
    decodeRows rows076 * decodeRows linearSecondRows = decodeRows rows100 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.LinearEnumeration
