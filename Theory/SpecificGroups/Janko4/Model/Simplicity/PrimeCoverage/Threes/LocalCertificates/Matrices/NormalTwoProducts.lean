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
theorem product_uPow2 : packedMul uRows uRows = uPow2Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_uv20 : packedMul uPow2Rows packedOne = uv20Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal200 : packedMul uv20Rows packedOne = normal200Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal201 : packedMul uv20Rows zRows = normal201Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal202 : packedMul uv20Rows zPow2Rows = normal202Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_uv21 : packedMul uPow2Rows vRows = uv21Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal210 : packedMul uv21Rows packedOne = normal210Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal211 : packedMul uv21Rows zRows = normal211Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal212 : packedMul uv21Rows zPow2Rows = normal212Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_uv22 : packedMul uPow2Rows vPow2Rows = uv22Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal220 : packedMul uv22Rows packedOne = normal220Rows := by
  rw [packedOne_eq_uv00Rows]
  exact packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal221 : packedMul uv22Rows zRows = normal221Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_normal222 : packedMul uv22Rows zPow2Rows = normal222Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates
