module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Tables

/-!
# Checked matrix products for census fusion: Case1_3

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

namespace Case1_3

theorem product_00 : packedMul translate3Rows translate3Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_01 : packedMul translate3Rows e0Rows = odd1_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_02 : packedMul odd1_3Rows odd1_3Rows = odd1_3RowsP2 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_03 : packedMul odd1_3RowsP2 odd1_3Rows = odd1_3RowsP3 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_04 : packedMul odd1_3RowsP3 odd1_3RowsP3 = odd1_3RowsP6 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_05 : packedMul odd1_3RowsP6 odd1_3Rows = odd1_3RowsP7 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_06 : packedMul odd1_3RowsP7 odd1_3RowsP7 = odd1_3RowsP14 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_07 : packedMul odd1_3RowsP14 odd1_3Rows = odd1_3RowsP15 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_08 : packedMul odd1_3RowsP15 odd1_3RowsP15 = odd1_3RowsP30 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_09 : packedMul odd1_3RowsP30 odd1_3Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Case1_3
end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
