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

theorem product_mask6046_1 : packedMul e1Rows mask6046_2Rows = mask6046_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask7428_11 : packedMul e11Rows e12Rows = mask7428_11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask7428_10 : packedMul e10Rows mask7428_11Rows = mask7428_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask7428_8 : packedMul e8Rows mask7428_10Rows = mask7428_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask7428_2 : packedMul e2Rows mask7428_8Rows = mask7428_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx0left : packedMul e0Rows xRows = actionx0leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx0right : packedMul xRows e0Rows = actionx0leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony0left : packedMul e0Rows yRows = actiony0leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony0right : packedMul yRows e0Rows = actiony0leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx1left : packedMul e1Rows xRows = actionx1leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx1right : packedMul xRows mask3_0Rows = actionx1leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony1left : packedMul e1Rows yRows = actiony1leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony1right : packedMul yRows e2Rows = actiony1leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx2left : packedMul e2Rows xRows = actionx2leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx2right : packedMul xRows mask5_0Rows = actionx2leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony2left : packedMul e2Rows yRows = actiony2leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
