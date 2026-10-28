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

theorem product_360 : packedMul e2Rows r350Rows = r351Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_361 : packedMul e0Rows r351Rows = r110Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_362 : packedMul e6Rows r325Rows = r352Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_363 : packedMul e5Rows r352Rows = r353Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_364 : packedMul e4Rows r353Rows = r354Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_365 : packedMul e2Rows r354Rows = r355Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_366 : packedMul e1Rows r355Rows = r117Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_367 : packedMul e8Rows e12Rows = r356Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_368 : packedMul e7Rows r356Rows = r357Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_369 : packedMul e6Rows r357Rows = r358Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_370 : packedMul e5Rows r358Rows = r359Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_371 : packedMul e4Rows r359Rows = r360Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_372 : packedMul e3Rows r360Rows = r127Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_373 : packedMul e7Rows e12Rows = r361Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_374 : packedMul e4Rows r361Rows = r362Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_375 : packedMul e0Rows r362Rows = r136Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_376 : packedMul e6Rows r318Rows = r363Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_377 : packedMul e3Rows r363Rows = r364Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_378 : packedMul e2Rows r364Rows = r365Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_379 : packedMul e1Rows r365Rows = r142Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
