module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Tables

/-!
# Checked matrix products for census fusion: Case1_4

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

namespace Case1_4

theorem product_00 : packedMul translate4Rows translate4Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_01 : packedMul translate4Rows e0Rows = odd1_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_02 : packedMul odd1_4Rows odd1_4Rows = odd1_4RowsP2 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_03 : packedMul odd1_4RowsP2 odd1_4Rows = odd1_4RowsP3 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_04 : packedMul odd1_4RowsP3 odd1_4RowsP3 = odd1_4RowsP6 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_05 : packedMul odd1_4RowsP6 odd1_4Rows = odd1_4RowsP7 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_06 : packedMul odd1_4RowsP7 odd1_4RowsP7 = odd1_4RowsP14 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_07 : packedMul odd1_4RowsP14 odd1_4Rows = odd1_4RowsP15 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_08 : packedMul odd1_4RowsP15 odd1_4RowsP15 = odd1_4RowsP30 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_09 : packedMul odd1_4RowsP30 odd1_4Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Case1_4
end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
