module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Tables

/-!
# Kernel-checked packed products for outside fusion, part 2

See `Tables` for the mathematical words and ATLAS source.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Part2

theorem product_00 : packedMul e3Rows e4Rows = m2_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_01 : packedMul e2Rows m2_3Rows = m2_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_02 : packedMul xy7Rows m2_2Rows = r2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_03 : packedMul r2Rows r2Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_04 : packedMul r2Rows conj1Rows = q2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_05 : packedMul q2Rows q2Rows = q2p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_06 : packedMul q2p2Rows q2Rows = q2p3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_07 : packedMul q2p3Rows q2p3Rows = q2p6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_08 : packedMul q2p6Rows q2Rows = q2p7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_09 : packedMul q2p7Rows q2p7Rows = q2p14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_10 : packedMul q2p14Rows q2Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Part2
end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
