module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.Data

/-! Kernel-checked full-matrix products for the commuting diagonal factors.
The row arithmetic is transported by decode_packedMul. ATLAS provenance and
reproduction: DiagonalImage/source/README.md. -/

public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors
open GeneratorCertificates Simplicity.Elevens.BridgeCertificate

set_option maxRecDepth 10000 in
theorem sigmaFirst_square :
    decodeRows sigmaFirstRows * decodeRows sigmaFirstRows = 1 := by
  rw [← decode_packedOne, ← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  rw [← fastRow_eq]
  simp only [packedOne, get_ofFn]
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
theorem linearFirst_square :
    decodeRows linearFirstRows * decodeRows linearFirstRows = 1 := by
  rw [← decode_packedOne, ← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  rw [← fastRow_eq]
  simp only [packedOne, get_ofFn]
  fin_cases i <;> decide +kernel

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors
