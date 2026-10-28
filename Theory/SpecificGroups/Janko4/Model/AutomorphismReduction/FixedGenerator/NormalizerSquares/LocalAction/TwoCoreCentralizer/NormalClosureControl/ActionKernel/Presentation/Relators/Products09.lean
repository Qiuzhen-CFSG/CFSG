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

theorem product_180 : packedMul r57Rows r11Rows = r177Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_181 : packedMul r18Rows r177Rows = r178Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_182 : packedMul r7Rows r11Rows = r179Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_183 : packedMul r24Rows r2Rows = r180Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_184 : packedMul r179Rows r180Rows = r181Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_185 : packedMul r178Rows r181Rows = r182Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_186 : packedMul r176Rows r182Rows = r183Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_187 : packedMul r5Rows r6Rows = r184Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_188 : packedMul yRows r184Rows = r185Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_189 : packedMul r6Rows r3Rows = r186Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_190 : packedMul r16Rows r19Rows = r187Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_191 : packedMul r186Rows r187Rows = r188Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_192 : packedMul r185Rows r188Rows = r189Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_193 : packedMul r5Rows r12Rows = r190Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_194 : packedMul r6Rows r12Rows = r191Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_195 : packedMul r190Rows r191Rows = r192Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_196 : packedMul r8Rows r46Rows = r193Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_197 : packedMul r9Rows xRows = r194Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_198 : packedMul r193Rows r194Rows = r195Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_199 : packedMul r192Rows r195Rows = r196Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
