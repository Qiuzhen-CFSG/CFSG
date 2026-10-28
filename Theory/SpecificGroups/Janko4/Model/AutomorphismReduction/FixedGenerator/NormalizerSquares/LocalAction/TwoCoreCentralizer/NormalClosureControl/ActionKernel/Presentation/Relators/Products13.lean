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

theorem product_260 : packedMul r4Rows r253Rows = r257Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_261 : packedMul r256Rows r257Rows = r258Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_262 : packedMul r255Rows r258Rows = r259Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_263 : packedMul r19Rows r19Rows = r260Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_264 : packedMul r14Rows r67Rows = r261Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_265 : packedMul r260Rows r261Rows = r262Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_266 : packedMul r40Rows r23Rows = r263Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_267 : packedMul r7Rows r17Rows = r264Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_268 : packedMul r15Rows r264Rows = r265Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_269 : packedMul r263Rows r265Rows = r266Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_270 : packedMul r262Rows r266Rows = r267Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_271 : packedMul r259Rows r267Rows = r268Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_272 : packedMul r14Rows r16Rows = r269Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_273 : packedMul r6Rows r269Rows = r270Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_274 : packedMul r54Rows r10Rows = r271Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_275 : packedMul r155Rows r271Rows = r272Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_276 : packedMul r270Rows r272Rows = r273Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_277 : packedMul r24Rows r10Rows = r274Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_278 : packedMul r47Rows r274Rows = r275Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_279 : packedMul r56Rows r31Rows = r276Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
