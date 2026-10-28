module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.NormalForms.Products1

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
theorem normal200_mul_u : packedMul normal200Rows uRows = normal000Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal200_mul_v : packedMul normal200Rows vRows = normal210Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal201_mul_u : packedMul normal201Rows uRows = normal001Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal201_mul_v : packedMul normal201Rows vRows = normal211Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal202_mul_u : packedMul normal202Rows uRows = normal002Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal202_mul_v : packedMul normal202Rows vRows = normal212Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal210_mul_u : packedMul normal210Rows uRows = normal012Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal210_mul_v : packedMul normal210Rows vRows = normal220Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal211_mul_u : packedMul normal211Rows uRows = normal010Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal211_mul_v : packedMul normal211Rows vRows = normal221Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal212_mul_u : packedMul normal212Rows uRows = normal011Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal212_mul_v : packedMul normal212Rows vRows = normal222Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal220_mul_u : packedMul normal220Rows uRows = normal021Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal220_mul_v : packedMul normal220Rows vRows = normal200Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal221_mul_u : packedMul normal221Rows uRows = normal022Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal221_mul_v : packedMul normal221Rows vRows = normal201Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal222_mul_u : packedMul normal222Rows uRows = normal020Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal222_mul_v : packedMul normal222Rows vRows = normal202Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates
