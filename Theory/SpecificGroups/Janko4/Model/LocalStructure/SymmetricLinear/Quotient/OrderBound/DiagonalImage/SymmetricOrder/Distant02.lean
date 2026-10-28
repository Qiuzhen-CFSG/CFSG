module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.SymmetricOrder.Data

/-!
Full 112-dimensional matrix witnesses for the type-A4 presentation cover.
Source: ATLAS J4G1-f2r112B0 and J4G1-max4W1, attributed in Model.Data and
SymmetricLinear.Model. Reproduction and proof contract: source/README.md.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.SymmetricOrder
open GeneratorCertificates Simplicity.Elevens.BridgeCertificate

set_option maxRecDepth 10000 in
theorem product_02 :
    decodeRows s0Rows * decodeRows s2Rows = decodeRows p02Rows := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  rw [← fastRow_eq]
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
theorem product_20 :
    decodeRows s2Rows * decodeRows s0Rows = decodeRows p02Rows := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  rw [← fastRow_eq]
  fin_cases i <;> decide +kernel

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.SymmetricOrder
