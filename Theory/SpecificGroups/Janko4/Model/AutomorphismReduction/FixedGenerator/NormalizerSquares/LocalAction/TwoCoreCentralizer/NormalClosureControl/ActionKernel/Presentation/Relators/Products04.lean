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

theorem product_80 : packedMul r48Rows r48Rows = r77Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_81 : packedMul r22Rows xRows = r78Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_82 : packedMul r77Rows r78Rows = r79Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_83 : packedMul r76Rows r79Rows = r80Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_84 : packedMul r25Rows r4Rows = r81Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_85 : packedMul r33Rows r81Rows = r82Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_86 : packedMul r13Rows r3Rows = r83Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_87 : packedMul r34Rows r83Rows = r84Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_88 : packedMul r82Rows r84Rows = r85Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_89 : packedMul r12Rows r6Rows = r86Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_90 : packedMul r13Rows r86Rows = r87Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_91 : packedMul r3Rows r36Rows = r88Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_92 : packedMul r25Rows r88Rows = r89Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_93 : packedMul r87Rows r89Rows = r90Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_94 : packedMul r85Rows r90Rows = r91Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_95 : packedMul r19Rows r37Rows = r92Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_96 : packedMul r35Rows r40Rows = r93Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_97 : packedMul r92Rows r93Rows = r94Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_98 : packedMul r41Rows r35Rows = r95Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_99 : packedMul r36Rows r36Rows = r96Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
