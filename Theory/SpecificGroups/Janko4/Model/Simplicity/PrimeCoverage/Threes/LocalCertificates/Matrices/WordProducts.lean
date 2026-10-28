module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Matrices.Rows

/-!
# Kernel products for the two positive generator words

Every multiplication (including a right inverse certificate for each inverse)
is checked row by row with `decide +kernel`. See `Rows` for the source attribution.
-/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem product_uPrefix2 : packedMul programFstRows programSndRows = uPrefix2Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_uPrefix3 : packedMul uPrefix2Rows programFstRows = uPrefix3Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_uPrefix4 : packedMul uPrefix3Rows programSndRows = uPrefix4Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_uPrefix5 : packedMul uPrefix4Rows programSndRows = uPrefix5Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_uPrefix6 : packedMul uPrefix5Rows programSndRows = uPrefix6Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_uPrefix7 : packedMul uPrefix6Rows programSndRows = uPrefix7Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_u : packedMul uPrefix7Rows programSndRows = uRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_vPrefix2 : packedMul programFstRows programSndRows = vPrefix2Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_vPrefix3 : packedMul vPrefix2Rows programSndRows = vPrefix3Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_vPrefix4 : packedMul vPrefix3Rows programFstRows = vPrefix4Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_vPrefix5 : packedMul vPrefix4Rows programSndRows = vPrefix5Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_vPrefix6 : packedMul vPrefix5Rows programSndRows = vPrefix6Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_vPrefix7 : packedMul vPrefix6Rows programSndRows = vPrefix7Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_vPrefix8 : packedMul vPrefix7Rows programFstRows = vPrefix8Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_vPrefix9 : packedMul vPrefix8Rows programSndRows = vPrefix9Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_vPrefix10 : packedMul vPrefix9Rows programSndRows = vPrefix10Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_vPrefix11 : packedMul vPrefix10Rows programSndRows = vPrefix11Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_v : packedMul vPrefix11Rows programSndRows = vRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates
