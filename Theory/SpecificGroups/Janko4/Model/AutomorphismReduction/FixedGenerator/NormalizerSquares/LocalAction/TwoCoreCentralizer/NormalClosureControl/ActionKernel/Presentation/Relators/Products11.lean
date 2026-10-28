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

theorem product_220 : packedMul r47Rows r5Rows = r217Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_221 : packedMul r216Rows r217Rows = r218Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_222 : packedMul r215Rows r218Rows = r219Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_223 : packedMul r11Rows r3Rows = r220Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_224 : packedMul r42Rows r220Rows = r221Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_225 : packedMul r6Rows r56Rows = r222Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_226 : packedMul r14Rows r7Rows = r223Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_227 : packedMul r222Rows r223Rows = r224Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_228 : packedMul r221Rows r224Rows = r225Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_229 : packedMul r219Rows r225Rows = r226Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_230 : packedMul r4Rows r31Rows = r227Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_231 : packedMul r50Rows r227Rows = r228Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_232 : packedMul r46Rows r12Rows = r229Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_233 : packedMul r15Rows r16Rows = r230Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_234 : packedMul r229Rows r230Rows = r231Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_235 : packedMul r228Rows r231Rows = r232Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_236 : packedMul r13Rows r53Rows = r233Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_237 : packedMul r58Rows r233Rows = r234Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_238 : packedMul r8Rows r4Rows = r235Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_239 : packedMul r8Rows r1Rows = r236Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
