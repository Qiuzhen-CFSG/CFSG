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

theorem product_200 : packedMul r189Rows r196Rows = r197Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_201 : packedMul r1Rows r11Rows = r198Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_202 : packedMul r47Rows r38Rows = r199Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_203 : packedMul r24Rows r199Rows = r200Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_204 : packedMul r198Rows r200Rows = r201Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_205 : packedMul r58Rows r4Rows = r202Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_206 : packedMul r50Rows r202Rows = r203Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_207 : packedMul r33Rows r2Rows = r204Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_208 : packedMul r46Rows r204Rows = r205Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_209 : packedMul r203Rows r205Rows = r206Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_210 : packedMul r201Rows r206Rows = r207Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_211 : packedMul yRows r14Rows = r208Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_212 : packedMul r208Rows r146Rows = r209Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_213 : packedMul r32Rows r44Rows = r210Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_214 : packedMul r32Rows xRows = r211Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_215 : packedMul r210Rows r211Rows = r212Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_216 : packedMul r209Rows r212Rows = r213Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_217 : packedMul r8Rows r19Rows = r214Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_218 : packedMul r58Rows r214Rows = r215Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_219 : packedMul r8Rows r5Rows = r216Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
