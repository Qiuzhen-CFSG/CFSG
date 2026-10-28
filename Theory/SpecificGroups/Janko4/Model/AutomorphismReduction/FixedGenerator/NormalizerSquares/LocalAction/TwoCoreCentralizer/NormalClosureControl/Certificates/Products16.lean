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

theorem product_actiony10right : packedMul yRows mask5964_2Rows = actiony10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx11left : packedMul e11Rows xRows = actionx11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx11right : packedMul xRows mask2171_0Rows = actionx11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony11left : packedMul e11Rows yRows = actiony11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony11right : packedMul yRows e6Rows = actiony11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx12left : packedMul e12Rows xRows = actionx12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actionx12right : packedMul xRows mask6046_1Rows = actionx12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony12left : packedMul e12Rows yRows = actiony12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_actiony12right : packedMul yRows mask7428_2Rows = actiony12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
