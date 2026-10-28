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

theorem product_380 : packedMul e6Rows r339Rows = r366Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_381 : packedMul e5Rows r366Rows = r367Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_382 : packedMul e3Rows r367Rows = r368Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_383 : packedMul e1Rows r368Rows = r369Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_384 : packedMul e0Rows r369Rows = r149Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_385 : packedMul e9Rows e10Rows = r370Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_386 : packedMul e7Rows r370Rows = r371Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_387 : packedMul e3Rows r371Rows = r372Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_388 : packedMul e0Rows r372Rows = r161Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_389 : packedMul e8Rows e9Rows = r373Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_390 : packedMul e7Rows r373Rows = r374Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_391 : packedMul e6Rows r374Rows = r375Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_392 : packedMul e5Rows r375Rows = r376Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_393 : packedMul e3Rows r376Rows = r377Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_394 : packedMul e0Rows r377Rows = r171Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_395 : packedMul e4Rows r332Rows = r378Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_396 : packedMul e3Rows r378Rows = r379Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_397 : packedMul e1Rows r379Rows = r183Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_398 : packedMul e8Rows r319Rows = r380Rows :=
  packed_of_list _ _ _ (by decide +kernel)

theorem product_399 : packedMul e6Rows r380Rows = r381Rows :=
  packed_of_list _ _ _ (by decide +kernel)


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.ActionKernel.Presentation.Relators
