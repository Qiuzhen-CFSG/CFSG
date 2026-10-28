module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Matrices.Rows

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
theorem normal000_mul_u : packedMul normal000Rows uRows = normal100Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal000_mul_v : packedMul normal000Rows vRows = normal010Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal001_mul_u : packedMul normal001Rows uRows = normal101Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal001_mul_v : packedMul normal001Rows vRows = normal011Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal002_mul_u : packedMul normal002Rows uRows = normal102Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal002_mul_v : packedMul normal002Rows vRows = normal012Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal010_mul_u : packedMul normal010Rows uRows = normal112Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal010_mul_v : packedMul normal010Rows vRows = normal020Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal011_mul_u : packedMul normal011Rows uRows = normal110Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal011_mul_v : packedMul normal011Rows vRows = normal021Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal012_mul_u : packedMul normal012Rows uRows = normal111Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal012_mul_v : packedMul normal012Rows vRows = normal022Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal020_mul_u : packedMul normal020Rows uRows = normal121Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal020_mul_v : packedMul normal020Rows vRows = normal000Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal021_mul_u : packedMul normal021Rows uRows = normal122Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal021_mul_v : packedMul normal021Rows vRows = normal001Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal022_mul_u : packedMul normal022Rows uRows = normal120Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem normal022_mul_v : packedMul normal022Rows vRows = normal002Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates
