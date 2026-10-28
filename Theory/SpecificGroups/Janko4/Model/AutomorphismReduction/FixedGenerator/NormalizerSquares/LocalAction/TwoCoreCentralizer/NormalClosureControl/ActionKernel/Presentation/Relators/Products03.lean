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

theorem product_60 : packedMul r1Rows r16Rows = r58Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_61 : packedMul r6Rows r16Rows = r59Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_62 : packedMul r59Rows r21Rows = r60Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_63 : packedMul r60Rows r9Rows = r61Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_64 : packedMul r61Rows r9Rows = r62Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_65 : packedMul r24Rows r24Rows = r63Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_66 : packedMul r24Rows r5Rows = r64Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_67 : packedMul r63Rows r64Rows = packedOne :=
  packed_of_list _ _ _ (by
    simp only [packedOne, Vector.toList_ofFn]
    decide +kernel)

theorem product_68 : packedMul r3Rows r19Rows = r65Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_69 : packedMul r4Rows r65Rows = r66Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_70 : packedMul r4Rows r25Rows = r67Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_71 : packedMul r20Rows r2Rows = r68Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_72 : packedMul r67Rows r68Rows = r69Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_73 : packedMul r66Rows r69Rows = r70Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_74 : packedMul r27Rows r18Rows = r71Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_75 : packedMul r17Rows r11Rows = r72Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_76 : packedMul r22Rows r72Rows = r73Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_77 : packedMul r71Rows r73Rows = r74Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_78 : packedMul r3Rows r48Rows = r75Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_79 : packedMul yRows r75Rows = r76Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
