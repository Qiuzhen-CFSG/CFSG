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

theorem product_0 : packedMul yRows yRows = r0Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_1 : packedMul xRows xRows = packedOne :=
  packed_of_list _ _ _ (by
    simp only [packedOne, Vector.toList_ofFn]
    decide +kernel)

theorem product_2 : packedMul yRows r0Rows = packedOne :=
  packed_of_list _ _ _ (by
    simp only [packedOne, Vector.toList_ofFn]
    decide +kernel)

theorem product_3 : packedMul xRows r0Rows = r1Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_4 : packedMul xRows yRows = r2Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_5 : packedMul r2Rows r1Rows = r3Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_6 : packedMul r2Rows r3Rows = r4Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_7 : packedMul r1Rows r1Rows = r5Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_8 : packedMul r2Rows r4Rows = r6Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_9 : packedMul r3Rows r5Rows = r7Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_10 : packedMul r1Rows r4Rows = r8Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_11 : packedMul r3Rows r3Rows = r9Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_12 : packedMul r2Rows r6Rows = r10Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_13 : packedMul r2Rows r10Rows = r11Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_14 : packedMul r4Rows r5Rows = r12Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_15 : packedMul r7Rows r6Rows = r13Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_16 : packedMul r1Rows r3Rows = r14Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_17 : packedMul r8Rows r3Rows = r15Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_18 : packedMul r7Rows r5Rows = r16Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_19 : packedMul r3Rows r1Rows = r17Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
