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

theorem product_100 : packedMul r95Rows r96Rows = r97Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_101 : packedMul r94Rows r97Rows = r98Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_102 : packedMul r4Rows r12Rows = r99Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_103 : packedMul r34Rows r41Rows = r100Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_104 : packedMul r4Rows r100Rows = r101Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_105 : packedMul r99Rows r101Rows = r102Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_106 : packedMul r42Rows r49Rows = r103Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_107 : packedMul r50Rows r2Rows = r104Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_108 : packedMul r34Rows r104Rows = r105Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_109 : packedMul r103Rows r105Rows = r106Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_110 : packedMul r102Rows r106Rows = r107Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_111 : packedMul r51Rows r43Rows = r108Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_112 : packedMul r6Rows r108Rows = r109Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_113 : packedMul r109Rows r109Rows = r110Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_114 : packedMul r8Rows r30Rows = r111Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_115 : packedMul r52Rows r3Rows = r112Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_116 : packedMul r111Rows r112Rows = r113Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_117 : packedMul r4Rows r30Rows = r114Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_118 : packedMul r52Rows r2Rows = r115Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_119 : packedMul r114Rows r115Rows = r116Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
