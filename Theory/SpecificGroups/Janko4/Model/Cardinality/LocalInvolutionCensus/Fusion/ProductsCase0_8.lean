module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Tables

/-!
# Checked matrix products for census fusion: Case0_8

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

namespace Case0_8

theorem product_00 : packedMul rep8Rows rep8Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

theorem product_01 : packedMul rep8Rows aztRows = odd0_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_02 : packedMul odd0_8Rows odd0_8Rows = odd0_8RowsP2 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_03 : packedMul odd0_8RowsP2 odd0_8Rows = odd0_8RowsP3 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_04 : packedMul odd0_8RowsP3 odd0_8RowsP3 = odd0_8RowsP6 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_05 : packedMul odd0_8RowsP6 odd0_8Rows = odd0_8RowsP7 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_06 : packedMul odd0_8RowsP7 odd0_8RowsP7 = odd0_8RowsP14 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_07 : packedMul odd0_8RowsP14 odd0_8RowsP14 = odd0_8RowsP28 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_08 : packedMul odd0_8RowsP28 odd0_8Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

end Case0_8
end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
