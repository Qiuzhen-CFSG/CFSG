module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Tables

/-!
# Checked matrix products for census fusion: Case1_2

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

namespace Case1_2

theorem product_00 : packedMul translate2Rows translate2Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_01 : packedMul translate2Rows bbbzaRows = odd1_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_02 : packedMul odd1_2Rows odd1_2Rows = odd1_2RowsP2 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_03 : packedMul odd1_2RowsP2 odd1_2RowsP2 = odd1_2RowsP4 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_04 : packedMul odd1_2RowsP4 odd1_2Rows = odd1_2RowsP5 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_05 : packedMul odd1_2RowsP5 odd1_2RowsP5 = odd1_2RowsP10 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_06 : packedMul odd1_2RowsP10 odd1_2Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Case1_2
end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
