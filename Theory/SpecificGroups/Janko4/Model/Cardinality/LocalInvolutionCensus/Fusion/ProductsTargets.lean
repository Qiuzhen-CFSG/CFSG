module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Tables

/-!
# Checked matrix products for census fusion: Common

Each packed GF(2) multiplication is proved by Lean kernel reduction.
The source words and attribution are documented in `Tables` and `source/README.md`.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation
open Janko4.GeneratorCertificates
open Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations (decoded_product eval_mul eval_inv)

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Common

theorem product_10 : packedMul bRows bRows = bSquareRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_11 : packedMul bSquareRows bRows = bCubeRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_12 : packedMul bSquareRows bSquareRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_13 : packedMul bCubeRows bRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_14 : packedMul aRows e0Rows = aztRowsL :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_15 : packedMul aztRowsL aRows = aztRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_16 : packedMul bSquareRows aRows = bbzaRowsL :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_17 : packedMul bbzaRowsL bSquareRows = bbzaRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_18 : packedMul bCubeRows aRows = bbbzaRowsL :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_19 : packedMul bbbzaRowsL bRows = bbbzaRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Common
end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
