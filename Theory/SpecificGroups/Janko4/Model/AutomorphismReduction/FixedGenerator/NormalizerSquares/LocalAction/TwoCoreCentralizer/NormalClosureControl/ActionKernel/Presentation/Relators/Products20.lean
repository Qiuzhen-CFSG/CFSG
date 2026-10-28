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

theorem product_400 : packedMul e5Rows r381Rows = r382Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_401 : packedMul e4Rows r382Rows = r383Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_402 : packedMul e3Rows r383Rows = r384Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_403 : packedMul e2Rows r384Rows = r385Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_404 : packedMul e1Rows r385Rows = r386Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_405 : packedMul e0Rows r386Rows = r197Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_406 : packedMul e6Rows e7Rows = r387Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_407 : packedMul e1Rows r387Rows = r388Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_408 : packedMul e0Rows r388Rows = r207Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_409 : packedMul e8Rows r345Rows = r389Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_410 : packedMul e7Rows r389Rows = r390Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_411 : packedMul e5Rows r390Rows = r391Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_412 : packedMul e3Rows r391Rows = r392Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_413 : packedMul e2Rows r392Rows = r393Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_414 : packedMul e1Rows r393Rows = r213Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_415 : packedMul e3Rows r326Rows = r394Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_416 : packedMul e2Rows r394Rows = r395Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_417 : packedMul e0Rows r395Rows = r226Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_418 : packedMul e8Rows r338Rows = r396Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_419 : packedMul e7Rows r396Rows = r397Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
