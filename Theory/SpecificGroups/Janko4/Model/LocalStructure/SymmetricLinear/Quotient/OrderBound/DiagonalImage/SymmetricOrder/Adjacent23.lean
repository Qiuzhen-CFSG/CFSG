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
theorem product_23 :
    decodeRows s2Rows * decodeRows sigmaFirstRows = decodeRows p23Rows := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  rw [← fastRow_eq]
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
theorem square_23 :
    decodeRows p23Rows * decodeRows p23Rows = decodeRows q23Rows := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  rw [← fastRow_eq]
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
theorem cube_23 :
    decodeRows q23Rows * decodeRows p23Rows = 1 := by
  rw [← decode_packedOne, ← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  rw [← fastRow_eq]
  simp only [packedOne, get_ofFn]
  fin_cases i <;> decide +kernel

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.SymmetricOrder
