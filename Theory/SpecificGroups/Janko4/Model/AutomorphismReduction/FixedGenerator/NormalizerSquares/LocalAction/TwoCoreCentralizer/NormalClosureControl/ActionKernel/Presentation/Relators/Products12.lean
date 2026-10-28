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

theorem product_240 : packedMul r235Rows r236Rows = r237Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_241 : packedMul r234Rows r237Rows = r238Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_242 : packedMul r232Rows r238Rows = r239Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_243 : packedMul r40Rows r14Rows = r240Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_244 : packedMul r5Rows r240Rows = r241Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_245 : packedMul r7Rows r16Rows = r242Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_246 : packedMul r62Rows r15Rows = r243Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_247 : packedMul r242Rows r243Rows = r244Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_248 : packedMul r241Rows r244Rows = r245Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_249 : packedMul r53Rows r13Rows = r246Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_250 : packedMul r38Rows r246Rows = r247Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_251 : packedMul r1Rows r40Rows = r248Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_252 : packedMul r13Rows r17Rows = r249Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_253 : packedMul r248Rows r249Rows = r250Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_254 : packedMul r247Rows r250Rows = r251Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_255 : packedMul r245Rows r251Rows = r252Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_256 : packedMul r17Rows r7Rows = r253Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_257 : packedMul r16Rows r25Rows = r254Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_258 : packedMul r253Rows r254Rows = r255Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_259 : packedMul r9Rows r14Rows = r256Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
