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

theorem product_440 : packedMul e9Rows e12Rows = r414Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_441 : packedMul e7Rows r414Rows = r415Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_442 : packedMul e5Rows r415Rows = r416Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_443 : packedMul e4Rows r416Rows = r293Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_444 : packedMul e7Rows r325Rows = r417Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_445 : packedMul e6Rows r417Rows = r418Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_446 : packedMul e2Rows r418Rows = r419Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_447 : packedMul e1Rows r419Rows = r420Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_448 : packedMul e0Rows r420Rows = r303Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_449 : packedMul e8Rows r318Rows = r421Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_450 : packedMul e7Rows r421Rows = r422Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_451 : packedMul e6Rows r422Rows = r423Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_452 : packedMul e4Rows r423Rows = r424Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_453 : packedMul e3Rows r424Rows = r425Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_454 : packedMul e2Rows r425Rows = r426Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_455 : packedMul e1Rows r426Rows = r317Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
