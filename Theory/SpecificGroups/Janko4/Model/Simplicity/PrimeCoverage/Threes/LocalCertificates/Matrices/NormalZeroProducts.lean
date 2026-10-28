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
theorem product_uv00 : packedMul packedOne packedOne = uv00Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal000 : packedMul uv00Rows packedOne = normal000Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal001 : packedMul uv00Rows zRows = normal001Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_zPow2 : packedMul zRows zRows = zPow2Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal002 : packedMul uv00Rows zPow2Rows = normal002Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_uv01 : packedMul packedOne vRows = uv01Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal010 : packedMul uv01Rows packedOne = normal010Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal011 : packedMul uv01Rows zRows = normal011Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal012 : packedMul uv01Rows zPow2Rows = normal012Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_vPow2 : packedMul vRows vRows = vPow2Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_uv02 : packedMul packedOne vPow2Rows = uv02Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal020 : packedMul uv02Rows packedOne = normal020Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal021 : packedMul uv02Rows zRows = normal021Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal022 : packedMul uv02Rows zPow2Rows = normal022Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates
