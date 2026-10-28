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

theorem product_120 : packedMul r113Rows r116Rows = r117Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_121 : packedMul r8Rows r31Rows = r118Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_122 : packedMul r41Rows r22Rows = r119Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_123 : packedMul r6Rows r119Rows = r120Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_124 : packedMul r118Rows r120Rows = r121Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_125 : packedMul r17Rows r21Rows = r122Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_126 : packedMul r38Rows r122Rows = r123Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_127 : packedMul r17Rows r10Rows = r124Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_128 : packedMul r6Rows r124Rows = r125Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_129 : packedMul r123Rows r125Rows = r126Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_130 : packedMul r121Rows r126Rows = r127Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_131 : packedMul r5Rows r4Rows = r128Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_132 : packedMul r25Rows r34Rows = r129Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_133 : packedMul r39Rows r129Rows = r130Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_134 : packedMul r128Rows r130Rows = r131Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_135 : packedMul r53Rows r8Rows = r132Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_136 : packedMul r8Rows r25Rows = r133Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_137 : packedMul r4Rows r133Rows = r134Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_138 : packedMul r132Rows r134Rows = r135Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_139 : packedMul r131Rows r135Rows = r136Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
