module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Tables

/-!
# Kernel-checked packed products for outside fusion, part 3

See `Tables` for the mathematical words and ATLAS source.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Part3

theorem product_00 : packedMul e4Rows e5Rows = m3_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_01 : packedMul e1Rows m3_4Rows = m3_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_02 : packedMul xy7Rows m3_1Rows = r3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_03 : packedMul r3Rows r3Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_04 : packedMul r3Rows conj1Rows = q3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_05 : packedMul q3Rows q3Rows = q3p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_06 : packedMul q3p2Rows q3p2Rows = q3p4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_07 : packedMul q3p4Rows q3Rows = q3p5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_08 : packedMul q3p5Rows q3p5Rows = q3p10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_09 : packedMul q3p10Rows q3p10Rows = q3p20Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_10 : packedMul q3p20Rows q3Rows = q3p21Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_11 : packedMul q3p21Rows q3p21Rows = q3p42Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_12 : packedMul q3p42Rows q3Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Part3
end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
