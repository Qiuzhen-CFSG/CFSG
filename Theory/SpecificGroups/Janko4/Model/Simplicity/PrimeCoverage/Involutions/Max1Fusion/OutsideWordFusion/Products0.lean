module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Tables

/-!
# Kernel-checked packed products for outside fusion, part 0

See `Tables` for the mathematical words and ATLAS source.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Part0

theorem product_00 : packedMul xy4Rows xy2Rows = xy6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_01 : packedMul xy6Rows xyRows = xy7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_02 : packedMul bRows wi0Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_03 : packedMul bRows bRows = w1_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_04 : packedMul w1_1Rows wi1Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_05 : packedMul bRows bRows = w2_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_06 : packedMul w2_1Rows aRows = w2_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_07 : packedMul w2_2Rows bRows = w2_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_08 : packedMul w2_3Rows bRows = w2_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_09 : packedMul w2_4Rows bRows = w2_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_10 : packedMul w2_5Rows bRows = w2_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_11 : packedMul w2_6Rows bRows = w2_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_12 : packedMul w2_7Rows bRows = w2_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_13 : packedMul w2_8Rows aRows = w2_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_14 : packedMul w2_9Rows wi2Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_15 : packedMul bRows d5Rows = conj0RowsL :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_16 : packedMul conj0RowsL wi0Rows = conj0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_17 : packedMul w1_1Rows d5Rows = conj1RowsL :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_18 : packedMul conj1RowsL wi1Rows = conj1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_19 : packedMul w2_9Rows d5Rows = conj2RowsL :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_20 : packedMul conj2RowsL wi2Rows = conj2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_21 : packedMul bRows aRows = conj3RowsL :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_22 : packedMul conj3RowsL wi0Rows = conj3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Part0
end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
