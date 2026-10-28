module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Tables

/-!
# Kernel-checked packed products for outside fusion, part 9

See `Tables` for the mathematical words and ATLAS source.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Part9

theorem product_00 : packedMul e6Rows e7Rows = m9_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_01 : packedMul e5Rows m9_6Rows = m9_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_02 : packedMul e4Rows m9_5Rows = m9_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_03 : packedMul e3Rows m9_4Rows = m9_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_04 : packedMul e2Rows m9_3Rows = m9_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_05 : packedMul e1Rows m9_2Rows = m9_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_06 : packedMul xy7Rows m9_1Rows = r9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_07 : packedMul r9Rows r9Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_08 : packedMul r9Rows conj3Rows = q9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_09 : packedMul q9Rows q9Rows = q9p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_10 : packedMul q9p2Rows q9p2Rows = q9p4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_11 : packedMul q9p4Rows q9Rows = q9p5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_12 : packedMul q9p5Rows q9p5Rows = q9p10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_13 : packedMul q9p10Rows q9Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Part9
end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
