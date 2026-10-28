module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Tables

/-!
# Kernel-checked packed products for outside fusion, part 6

See `Tables` for the mathematical words and ATLAS source.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Part6

theorem product_00 : packedMul e3Rows e7Rows = m6_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_01 : packedMul e1Rows m6_3Rows = m6_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_02 : packedMul xy7Rows m6_1Rows = r6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_03 : packedMul r6Rows r6Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_04 : packedMul r6Rows conj2Rows = q6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_05 : packedMul q6Rows q6Rows = q6p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_06 : packedMul q6p2Rows q6Rows = q6p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_07 : packedMul q6p3Rows q6p3Rows = q6p6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_08 : packedMul q6p6Rows q6Rows = q6p7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_09 : packedMul q6p7Rows q6p7Rows = q6p14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_10 : packedMul q6p14Rows q6p14Rows = q6p28Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_11 : packedMul q6p28Rows q6Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Part6
end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
