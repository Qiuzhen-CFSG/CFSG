module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Tables

/-!
# Kernel-checked packed products for outside fusion, part 8

See `Tables` for the mathematical words and ATLAS source.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Part8

theorem product_00 : packedMul e6Rows e7Rows = m8_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_01 : packedMul e4Rows m8_6Rows = m8_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_02 : packedMul xy7Rows m8_4Rows = r8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_03 : packedMul r8Rows r8Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_04 : packedMul r8Rows d5Rows = q8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_05 : packedMul q8Rows q8Rows = q8p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_06 : packedMul q8p2Rows q8p2Rows = q8p4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_07 : packedMul q8p4Rows q8Rows = q8p5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_08 : packedMul q8p5Rows q8p5Rows = q8p10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_09 : packedMul q8p10Rows q8p10Rows = q8p20Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_10 : packedMul q8p20Rows q8Rows = q8p21Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_11 : packedMul q8p21Rows q8p21Rows = q8p42Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_12 : packedMul q8p42Rows q8Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Part8
end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
