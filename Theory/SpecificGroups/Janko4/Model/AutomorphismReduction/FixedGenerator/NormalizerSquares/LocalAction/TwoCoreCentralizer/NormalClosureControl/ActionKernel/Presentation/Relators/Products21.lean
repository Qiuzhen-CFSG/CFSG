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

theorem product_420 : packedMul e5Rows r397Rows = r398Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_421 : packedMul e4Rows r398Rows = r399Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_422 : packedMul e3Rows r399Rows = r400Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_423 : packedMul e2Rows r400Rows = r401Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_424 : packedMul e1Rows r401Rows = r402Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_425 : packedMul e0Rows r402Rows = r239Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_426 : packedMul e5Rows r363Rows = r403Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_427 : packedMul e3Rows r403Rows = r404Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_428 : packedMul e2Rows r404Rows = r405Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_429 : packedMul e1Rows r405Rows = r252Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_430 : packedMul e5Rows e9Rows = r406Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_431 : packedMul e2Rows r406Rows = r407Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_432 : packedMul e1Rows r407Rows = r408Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_433 : packedMul e0Rows r408Rows = r268Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_434 : packedMul e9Rows r330Rows = r409Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_435 : packedMul e8Rows r409Rows = r410Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_436 : packedMul e6Rows r410Rows = r411Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_437 : packedMul e4Rows r411Rows = r412Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_438 : packedMul e3Rows r412Rows = r413Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_439 : packedMul e2Rows r413Rows = r279Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
