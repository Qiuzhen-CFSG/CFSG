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
theorem product_086_1 :
    decodeRows rows086 * decodeRows linearSecondRows = decodeRows rows110 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_088_0 :
    decodeRows rows088 * decodeRows linearFirstRows = decodeRows rows111 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_088_1 :
    decodeRows rows088 * decodeRows linearSecondRows = decodeRows rows112 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_089_1 :
    decodeRows rows089 * decodeRows linearSecondRows = decodeRows rows113 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_090_0 :
    decodeRows rows090 * decodeRows linearFirstRows = decodeRows rows114 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_090_1 :
    decodeRows rows090 * decodeRows linearSecondRows = decodeRows rows115 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_091_0 :
    decodeRows rows091 * decodeRows linearFirstRows = decodeRows rows116 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_092_1 :
    decodeRows rows092 * decodeRows linearSecondRows = decodeRows rows117 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_093_0 :
    decodeRows rows093 * decodeRows linearFirstRows = decodeRows rows118 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_094_1 :
    decodeRows rows094 * decodeRows linearSecondRows = decodeRows rows119 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_095_0 :
    decodeRows rows095 * decodeRows linearFirstRows = decodeRows rows120 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_095_1 :
    decodeRows rows095 * decodeRows linearSecondRows = decodeRows rows092 := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro r
  rw [← fastRow_eq]
  fin_cases r <;> decide +kernel

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.LinearEnumeration
