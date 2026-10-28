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

theorem product_40 : packedMul r4Rows r4Rows = r38Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_41 : packedMul r30Rows r7Rows = r39Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_42 : packedMul r10Rows r3Rows = r40Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_43 : packedMul r8Rows r37Rows = r41Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_44 : packedMul r35Rows r4Rows = r42Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_45 : packedMul r27Rows r3Rows = r43Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_46 : packedMul r26Rows r15Rows = r44Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_47 : packedMul r33Rows r10Rows = r45Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_48 : packedMul r26Rows r8Rows = r46Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_49 : packedMul r8Rows r13Rows = r47Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_50 : packedMul r22Rows r4Rows = r48Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_51 : packedMul r11Rows r5Rows = r49Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_52 : packedMul r3Rows r14Rows = r50Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_53 : packedMul r22Rows r11Rows = r51Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_54 : packedMul r17Rows r16Rows = r52Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_55 : packedMul r17Rows r32Rows = r53Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_56 : packedMul r8Rows r39Rows = r54Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_57 : packedMul r45Rows r31Rows = r55Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_58 : packedMul r55Rows r11Rows = r56Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_59 : packedMul r10Rows r5Rows = r57Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
