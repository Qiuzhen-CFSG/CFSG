module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.Rows
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.FastArithmetic

/-!
# Certified lifts of the max2 quotient relators

Shared subwords factor the explicit words in `Presentation.Data`. The original
ATLAS max2 matrices and thirteen normal-closure generators are already checked
in `CentralizerReduction`. Each additional product is checked by kernel reduction
of the proved packed arithmetic; Python supplies witnesses only. The resulting
relator lifts are actual words in the relative normal closure, with no local
identification or order assumed. See `Presentation/source/README.md`.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem product_280 : packedMul r276Rows r236Rows = r277Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_281 : packedMul r275Rows r277Rows = r278Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_282 : packedMul r273Rows r278Rows = r279Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_283 : packedMul r38Rows r6Rows = r280Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_284 : packedMul r7Rows r280Rows = r281Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_285 : packedMul r38Rows r41Rows = r282Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_286 : packedMul r51Rows r10Rows = r283Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_287 : packedMul r282Rows r283Rows = r284Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_288 : packedMul r281Rows r284Rows = r285Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_289 : packedMul r11Rows r57Rows = r286Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_290 : packedMul r4Rows r3Rows = r287Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_291 : packedMul r286Rows r287Rows = r288Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_292 : packedMul r23Rows r15Rows = r289Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_293 : packedMul r32Rows r2Rows = r290Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_294 : packedMul r289Rows r290Rows = r291Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_295 : packedMul r288Rows r291Rows = r292Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_296 : packedMul r285Rows r292Rows = r293Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_297 : packedMul r4Rows r1Rows = r294Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_298 : packedMul r9Rows r294Rows = r295Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_299 : packedMul r47Rows r52Rows = r296Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
