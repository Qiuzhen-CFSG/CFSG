module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePairTables

/-! # Checked native pair displacement ranks

Every multiplication and row expansion is checked by Lean's kernel.
See `NativePairTables` for the mathematical invariant and source.
-/

public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePair
open Janko4.GeneratorCertificates Cardinality.KernelCount
open Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem native_rank : (decodeRows nativeProductRows).rank = 20 := by
  apply rank_certificate nativeProductRows nativeBasis nativeFromRows nativeFromBasis nativePivots
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem census_rank : (decodeRows censusProductRows).rank = 16 := by
  apply rank_certificate censusProductRows censusBasis censusFromRows censusFromBasis censusPivots
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem product_m18 : packedMul e1Rows e4Rows = m18Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m50 : packedMul m18Rows e5Rows = m50Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m306 : packedMul m50Rows e8Rows = m306Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m818 : packedMul m306Rows e9Rows = m818Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m9 : packedMul e0Rows e3Rows = m9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m41 : packedMul m9Rows e5Rows = m41Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m169 : packedMul m41Rows e7Rows = m169Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m425 : packedMul m169Rows e8Rows = m425Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_m1449 : packedMul m425Rows e10Rows = m1449Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_native : packedMul (displacement m818Rows) (displacement m1449Rows) = nativeProductRows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, displacement, get_ofFn]
    decide +kernel)

theorem product_census : packedMul (displacement r1) (displacement r2) = censusProductRows :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedRow, displacement, r1, r2, get_ofFn]
    decide +kernel)

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePair
