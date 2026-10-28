module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.Data

/-! Numerical coordinate products for the literal max4 flag. The packed rows
use ATLAS J4G1-f2r112B0 and J4G1-max4W1; see OrderBound/source/README.md.
Each row identity is checked by the kernel and transported by decode_packedMul. -/

public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound
open GeneratorCertificates CharacteristicTwo.Coordinates
open Simplicity.Elevens.BridgeCertificate NormalFour.Certificate

set_option maxRecDepth 10000 in
theorem second_step : decodeRows basisRows * decodeRows v025 = decodeRows secondStepRows := by
  rw [← decode_packedMul]
  apply congrArg decodeRows
  apply packedMul_eq_of_rows
  intro i
  rw [← fastRow_eq]
  fin_cases i <;> decide +kernel

end Janko4.LocalStructure.SymmetricLinear.OrderBound
