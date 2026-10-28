module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.Certificates.Rows

/-!
# Kernel-checked max2 normal-closure witnesses

These products use the original ATLAS `J4G1-max2W1` outputs and the thirteen
words in `NormalClosureControl.Generators`. Source matrices and conventions
are documented in `Janko4.Model.Data`; the word bridge is in `Max2Bridge`.
`source/generate.py` produces untrusted witnesses. `decide +kernel` checks
packed products, and `decode_packedMul` identifies them with matrix products.
No group order or quotient faithfulness is assumed.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem product_actiony2right : packedMul yRows e3Rows = actiony2leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx3left : packedMul e3Rows xRows = actionx3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx3right : packedMul xRows e4Rows = actionx3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony3left : packedMul e3Rows yRows = actiony3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony3right : packedMul yRows e1Rows = actiony3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx4left : packedMul e4Rows xRows = actionx4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx4right : packedMul xRows e3Rows = actionx4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony4left : packedMul e4Rows yRows = actiony4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony4right : packedMul yRows e5Rows = actiony4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx5left : packedMul e5Rows xRows = actionx5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx5right : packedMul xRows e6Rows = actionx5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony5left : packedMul e5Rows yRows = actiony5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony5right : packedMul yRows e7Rows = actiony5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx6left : packedMul e6Rows xRows = actionx6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx6right : packedMul xRows e5Rows = actionx6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony6left : packedMul e6Rows yRows = actiony6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
