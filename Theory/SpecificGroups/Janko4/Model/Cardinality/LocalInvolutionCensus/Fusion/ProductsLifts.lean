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

theorem product_00 : packedMul xyRows xyRows = xyRowsP2 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_01 : packedMul xyRowsP2 xyRows = xyRowsP3 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_02 : packedMul xyRowsP3 xyRowsP3 = xyRowsP6 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_03 : packedMul xyRowsP6 xyRows = lift2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_04 : packedMul xyRows xyRows = xyRowsP2 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_05 : packedMul xyRowsP2 xyRowsP2 = xyRowsP4 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_06 : packedMul xyRowsP4 xyRows = xy5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_07 : packedMul xy5Rows w14Rows = lift3BaseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_08 : packedMul lift3BaseRows lift3BaseRows = lift3BaseRowsP2 :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_09 : packedMul lift3BaseRowsP2 lift3BaseRowsP2 = lift3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Common
end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
