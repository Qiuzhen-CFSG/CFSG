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

theorem product_20 : packedMul r12Rows r5Rows = r18Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_21 : packedMul r14Rows r8Rows = r19Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_22 : packedMul r9Rows r12Rows = r20Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_23 : packedMul r6Rows r5Rows = r21Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_24 : packedMul r4Rows r13Rows = r22Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_25 : packedMul r18Rows r20Rows = r23Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_26 : packedMul r5Rows r5Rows = r24Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_27 : packedMul r2Rows r11Rows = r25Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_28 : packedMul r15Rows r23Rows = r26Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_29 : packedMul r1Rows r13Rows = r27Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_30 : packedMul r9Rows r3Rows = r28Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_31 : packedMul r28Rows r21Rows = r29Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_32 : packedMul r29Rows r11Rows = r30Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_33 : packedMul r1Rows r9Rows = r31Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_34 : packedMul r7Rows r3Rows = r32Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_35 : packedMul r9Rows r1Rows = r33Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_36 : packedMul r1Rows r6Rows = r34Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_37 : packedMul r4Rows r7Rows = r35Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_38 : packedMul r2Rows r2Rows = r36Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_39 : packedMul r19Rows r6Rows = r37Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
