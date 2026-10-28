module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Matrices.Rows

/-!
# Kernel products for the literal ATLAS program

Every multiplication (including a right inverse certificate for each inverse)
is checked row by row with `decide +kernel`. See `Rows` for the source attribution.
-/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem product_ab : packedMul aRows bRows = abRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_ba : packedMul bRows aRows = baRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_abPow2 : packedMul abRows abRows = abPow2Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_abPow3 : packedMul abRows abPow2Rows = abPow3Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_abCubeB : packedMul abPow3Rows bRows = abCubeBRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_abCubeBPow2 : packedMul abCubeBRows abCubeBRows = abCubeBPow2Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_abCubeBPow4 : packedMul abCubeBPow2Rows abCubeBPow2Rows = abCubeBPow4Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_abPow4 : packedMul abPow2Rows abPow2Rows = abPow4Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_abPow8 : packedMul abPow4Rows abPow4Rows = abPow8Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_abPow16 : packedMul abPow8Rows abPow8Rows = abPow16Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_ab16Inv : packedMul abPow16Rows ab16InvRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_baPow2 : packedMul baRows baRows = baPow2Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_baPow3 : packedMul baRows baPow2Rows = baPow3Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_baPow6 : packedMul baPow3Rows baPow3Rows = baPow6Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_baPow12 : packedMul baPow6Rows baPow6Rows = baPow12Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_baPow24 : packedMul baPow12Rows baPow12Rows = baPow24Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_conjSecond : packedMul ab16InvRows baPow24Rows = conjSecondRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_conjSecondInv : packedMul conjSecondRows conjSecondInvRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_secondLeft : packedMul conjSecondInvRows abCubeBPow4Rows = secondLeftRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_programSnd : packedMul secondLeftRows conjSecondRows = programSndRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_baPow4 : packedMul baPow2Rows baPow2Rows = baPow4Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_baPow8 : packedMul baPow4Rows baPow4Rows = baPow8Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_firstMid : packedMul abRows baPow8Rows = firstMidRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_abPow5 : packedMul abPow2Rows abPow3Rows = abPow5Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_abPow9 : packedMul abPow4Rows abPow5Rows = abPow9Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_abPow18 : packedMul abPow9Rows abPow9Rows = abPow18Rows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_conjFirst : packedMul firstMidRows abPow18Rows = conjFirstRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_conjFirstInv : packedMul conjFirstRows conjFirstInvRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_firstLeft : packedMul conjFirstInvRows aRows = firstLeftRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_programFst : packedMul firstLeftRows conjFirstRows = programFstRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates
