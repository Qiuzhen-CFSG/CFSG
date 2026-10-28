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

theorem product_340 : packedMul e5Rows r333Rows = r334Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_341 : packedMul e4Rows r334Rows = r335Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_342 : packedMul e3Rows r335Rows = r336Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_343 : packedMul e1Rows r336Rows = r91Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_344 : packedMul e10Rows e12Rows = r337Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_345 : packedMul e9Rows r337Rows = r338Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_346 : packedMul e7Rows r338Rows = r339Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_347 : packedMul e5Rows r339Rows = r340Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_348 : packedMul e4Rows r340Rows = r341Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_349 : packedMul e3Rows r341Rows = r342Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_350 : packedMul e2Rows r342Rows = r343Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_351 : packedMul e1Rows r343Rows = r344Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_352 : packedMul e0Rows r344Rows = r98Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_353 : packedMul e9Rows r331Rows = r345Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_354 : packedMul e3Rows r345Rows = r346Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_355 : packedMul e2Rows r346Rows = r347Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_356 : packedMul e1Rows r347Rows = r348Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_357 : packedMul e0Rows r348Rows = r107Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_358 : packedMul e6Rows r338Rows = r349Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_359 : packedMul e4Rows r349Rows = r350Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
