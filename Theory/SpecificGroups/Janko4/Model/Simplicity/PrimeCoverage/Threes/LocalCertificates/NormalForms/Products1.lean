module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.NormalForms.Products0

/-!
# Packed transition certificates for the 27 local J4 normal forms

Each equality checks the right action of one of the two proposed generators
on the packed rows, using kernel reduction and the proved packed multiplication
algorithm. The row witnesses and ATLAS source attribution are in `Matrices.Rows`.
Transport to the actual group words additionally requires their matrix evaluations.
-/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem normal100_mul_u : packedMul normal100Rows uRows = normal200Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal100_mul_v : packedMul normal100Rows vRows = normal110Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal101_mul_u : packedMul normal101Rows uRows = normal201Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal101_mul_v : packedMul normal101Rows vRows = normal111Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal102_mul_u : packedMul normal102Rows uRows = normal202Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal102_mul_v : packedMul normal102Rows vRows = normal112Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal110_mul_u : packedMul normal110Rows uRows = normal212Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal110_mul_v : packedMul normal110Rows vRows = normal120Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal111_mul_u : packedMul normal111Rows uRows = normal210Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal111_mul_v : packedMul normal111Rows vRows = normal121Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal112_mul_u : packedMul normal112Rows uRows = normal211Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal112_mul_v : packedMul normal112Rows vRows = normal122Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal120_mul_u : packedMul normal120Rows uRows = normal221Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal120_mul_v : packedMul normal120Rows vRows = normal100Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal121_mul_u : packedMul normal121Rows uRows = normal222Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal121_mul_v : packedMul normal121Rows vRows = normal101Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal122_mul_u : packedMul normal122Rows uRows = normal220Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal122_mul_v : packedMul normal122Rows vRows = normal102Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates
