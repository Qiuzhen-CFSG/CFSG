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

theorem product_actiony6right : packedMul yRows e8Rows = actiony6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx7left : packedMul e7Rows xRows = actionx7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx7right : packedMul xRows e9Rows = actionx7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony7left : packedMul e7Rows yRows = actiony7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony7right : packedMul yRows e4Rows = actiony7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx8left : packedMul e8Rows xRows = actionx8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx8right : packedMul xRows e10Rows = actionx8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony8left : packedMul e8Rows yRows = actiony8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony8right : packedMul yRows e11Rows = actiony8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx9left : packedMul e9Rows xRows = actionx9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx9right : packedMul xRows e7Rows = actionx9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony9left : packedMul e9Rows yRows = actiony9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony9right : packedMul yRows e12Rows = actiony9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx10left : packedMul e10Rows xRows = actionx10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx10right : packedMul xRows e8Rows = actionx10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony10left : packedMul e10Rows yRows = actiony10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
