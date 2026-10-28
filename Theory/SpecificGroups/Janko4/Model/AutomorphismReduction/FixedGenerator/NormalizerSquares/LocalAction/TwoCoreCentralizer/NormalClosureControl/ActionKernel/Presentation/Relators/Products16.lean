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

theorem product_320 : packedMul r309Rows r316Rows = r317Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_321 : packedMul e10Rows e11Rows = r318Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_322 : packedMul e9Rows r318Rows = r319Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_323 : packedMul e6Rows r319Rows = r320Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_324 : packedMul e5Rows r320Rows = r321Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_325 : packedMul e4Rows r321Rows = r322Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_326 : packedMul e1Rows r322Rows = r323Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_327 : packedMul e0Rows r323Rows = r70Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_328 : packedMul e2Rows e3Rows = r324Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_329 : packedMul e0Rows r324Rows = r74Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_330 : packedMul e9Rows e11Rows = r325Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_331 : packedMul e8Rows r325Rows = r326Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_332 : packedMul e7Rows r326Rows = r327Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_333 : packedMul e5Rows r327Rows = r328Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_334 : packedMul e4Rows r328Rows = r329Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_335 : packedMul e1Rows r329Rows = r80Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_336 : packedMul e11Rows e12Rows = r330Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_337 : packedMul e10Rows r330Rows = r331Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_338 : packedMul e8Rows r331Rows = r332Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_339 : packedMul e7Rows r332Rows = r333Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
