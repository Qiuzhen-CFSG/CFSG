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

theorem product_140 : packedMul r39Rows r49Rows = r137Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_141 : packedMul r19Rows r137Rows = r138Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_142 : packedMul r3Rows r54Rows = r139Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_143 : packedMul r11Rows r1Rows = r140Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_144 : packedMul r139Rows r140Rows = r141Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_145 : packedMul r138Rows r141Rows = r142Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_146 : packedMul yRows r3Rows = r143Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_147 : packedMul r44Rows r13Rows = r144Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_148 : packedMul r143Rows r144Rows = r145Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_149 : packedMul r44Rows r7Rows = r146Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_150 : packedMul r2Rows xRows = r147Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_151 : packedMul r146Rows r147Rows = r148Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_152 : packedMul r145Rows r148Rows = r149Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_153 : packedMul r7Rows r14Rows = r150Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_154 : packedMul r6Rows r150Rows = r151Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_155 : packedMul r43Rows r22Rows = r152Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_156 : packedMul r42Rows r152Rows = r153Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_157 : packedMul r151Rows r153Rows = r154Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_158 : packedMul r14Rows r34Rows = r155Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_159 : packedMul r12Rows r155Rows = r156Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
