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

theorem product_300 : packedMul r32Rows r296Rows = r297Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_301 : packedMul r295Rows r297Rows = r298Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_302 : packedMul r62Rows r216Rows = r299Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_303 : packedMul r7Rows r57Rows = r300Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_304 : packedMul r300Rows r243Rows = r301Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_305 : packedMul r299Rows r301Rows = r302Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_306 : packedMul r298Rows r302Rows = r303Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_307 : packedMul r25Rows r11Rows = r304Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_308 : packedMul r1Rows r304Rows = r305Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_309 : packedMul r9Rows r46Rows = r306Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_310 : packedMul r12Rows r15Rows = r307Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_311 : packedMul r306Rows r307Rows = r308Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_312 : packedMul r305Rows r308Rows = r309Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_313 : packedMul r18Rows r7Rows = r310Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_314 : packedMul r1Rows r7Rows = r311Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_315 : packedMul r310Rows r311Rows = r312Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_316 : packedMul r8Rows r54Rows = r313Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_317 : packedMul r11Rows r2Rows = r314Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_318 : packedMul r313Rows r314Rows = r315Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_319 : packedMul r312Rows r315Rows = r316Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
