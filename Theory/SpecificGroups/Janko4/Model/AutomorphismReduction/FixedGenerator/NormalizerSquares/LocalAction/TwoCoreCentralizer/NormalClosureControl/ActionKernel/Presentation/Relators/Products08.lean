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

theorem product_160 : packedMul r7Rows r4Rows = r157Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_161 : packedMul r27Rows r36Rows = r158Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_162 : packedMul r157Rows r158Rows = r159Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_163 : packedMul r156Rows r159Rows = r160Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_164 : packedMul r154Rows r160Rows = r161Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_165 : packedMul r7Rows r1Rows = r162Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_166 : packedMul r1Rows r162Rows = r163Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_167 : packedMul r27Rows r16Rows = r164Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_168 : packedMul r49Rows r164Rows = r165Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_169 : packedMul r163Rows r165Rows = r166Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_170 : packedMul r6Rows r72Rows = r167Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_171 : packedMul r31Rows r15Rows = r168Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_172 : packedMul r56Rows r168Rows = r169Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_173 : packedMul r167Rows r169Rows = r170Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_174 : packedMul r166Rows r170Rows = r171Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_175 : packedMul r43Rows r4Rows = r172Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_176 : packedMul r42Rows r172Rows = r173Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_177 : packedMul r45Rows r14Rows = r174Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_178 : packedMul r6Rows r174Rows = r175Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_179 : packedMul r173Rows r175Rows = r176Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
