module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.SeedCertificates.Tables

/-!
# Checked products for the two kernel fusion witnesses

Each equality is reduced by Lean's kernel using the packed GF(2) arithmetic
of `GeneratorCertificates.Packed`. See `Tables` for the words and source.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.SeedCertificates
open Janko4.Cardinality.KernelCount Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem product_00 : packedMul e0Rows e1Rows = pairRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_01 : packedMul e0Rows d5Rows = utRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_02 : packedMul utRows utRows = ut2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_03 : packedMul ut2Rows ut2Rows = ut4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_04 : packedMul ut4Rows ut4Rows = ut8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_05 : packedMul ut8Rows ut4Rows = ut12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_06 : packedMul ut12Rows ut2Rows = ut14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_07 : packedMul ut14Rows utRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_08 : packedMul pairRows aRows = vaRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_09 : packedMul vaRows vaRows = va2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_10 : packedMul va2Rows va2Rows = va4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_11 : packedMul va4Rows va4Rows = va8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_12 : packedMul va8Rows va2Rows = va10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_13 : packedMul va10Rows vaRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Janko4.Simplicity.Max1Fusion.SeedCertificates
