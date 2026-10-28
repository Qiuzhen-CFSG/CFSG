module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.Data

/-! Kernel-checked full-matrix products for the commuting diagonal factors.
The row arithmetic is transported by decode_packedMul. ATLAS provenance and
reproduction: DiagonalImage/source/README.md. -/

public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors
open GeneratorCertificates Simplicity.Elevens.BridgeCertificate

set_option maxRecDepth 10000 in
theorem first_reverse :
    decodeRows linearFirstRows * decodeRows sigmaFirstRows = decodeRows diagonalFirstRows := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  rw [← fastRow_eq]
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
theorem second_reverse :
    decodeRows linearSecondRows * decodeRows sigmaSecondRows = decodeRows diagonalSecondRows := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  rw [← fastRow_eq]
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
theorem cross_first_second_reverse :
    decodeRows linearSecondRows * decodeRows sigmaFirstRows = decodeRows crossFirstSecondRows := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  rw [← fastRow_eq]
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
theorem cross_second_first_reverse :
    decodeRows linearFirstRows * decodeRows sigmaSecondRows = decodeRows crossSecondFirstRows := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  rw [← fastRow_eq]
  fin_cases i <;> decide +kernel

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors
