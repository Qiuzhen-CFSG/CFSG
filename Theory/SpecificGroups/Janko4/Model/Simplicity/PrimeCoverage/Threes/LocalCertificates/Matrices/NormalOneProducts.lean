module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Matrices.IdentityRows

/-!
# Kernel products for the twenty-seven normal forms

Every multiplication (including a right inverse certificate for each inverse)
is checked row by row with `decide +kernel`. See `Rows` for the source attribution.
-/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem product_uv10 : packedMul uRows packedOne = uv10Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal100 : packedMul uv10Rows packedOne = normal100Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal101 : packedMul uv10Rows zRows = normal101Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal102 : packedMul uv10Rows zPow2Rows = normal102Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_uv11 : packedMul uRows vRows = uv11Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal110 : packedMul uv11Rows packedOne = normal110Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal111 : packedMul uv11Rows zRows = normal111Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal112 : packedMul uv11Rows zPow2Rows = normal112Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_uv12 : packedMul uRows vPow2Rows = uv12Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal120 : packedMul uv12Rows packedOne = normal120Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal121 : packedMul uv12Rows zRows = normal121Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal122 : packedMul uv12Rows zPow2Rows = normal122Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates
