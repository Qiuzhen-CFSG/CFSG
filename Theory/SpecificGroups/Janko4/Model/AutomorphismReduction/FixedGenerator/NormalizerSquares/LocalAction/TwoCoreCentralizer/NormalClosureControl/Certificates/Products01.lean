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

theorem product_word10left : packedMul e8Rows xRows = word10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word10right : packedMul xRows e10Rows = word10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word11left : packedMul e8Rows yRows = word11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word11right : packedMul yRows e11Rows = word11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word12left : packedMul e9Rows yRows = word12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word12right : packedMul yRows e12Rows = word12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_2left : packedMul e1Rows e2Rows = comm1_2leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_2right : packedMul e2Rows e1Rows = comm1_2leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_3left : packedMul e1Rows e3Rows = comm1_3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_3right : packedMul e3Rows e1Rows = comm1_3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_4left : packedMul e1Rows e4Rows = comm1_4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_4right : packedMul e4Rows e1Rows = comm1_4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_5left : packedMul e1Rows e5Rows = comm1_5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_5reverse : packedMul e5Rows e1Rows = comm1_5reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_5right : packedMul comm1_5reverseRows e0Rows = comm1_5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_6left : packedMul e1Rows e6Rows = comm1_6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
