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

theorem product_comm1_12right : packedMul comm1_12reverseRows e0Rows = comm1_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_3left : packedMul e2Rows e3Rows = comm2_3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_3right : packedMul e3Rows e2Rows = comm2_3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_4left : packedMul e2Rows e4Rows = comm2_4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_4right : packedMul e4Rows e2Rows = comm2_4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_5left : packedMul e2Rows e5Rows = comm2_5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_5right : packedMul e5Rows e2Rows = comm2_5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_6left : packedMul e2Rows e6Rows = comm2_6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_6right : packedMul e6Rows e2Rows = comm2_6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_7left : packedMul e2Rows e7Rows = comm2_7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_7reverse : packedMul e7Rows e2Rows = comm2_7reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_7right : packedMul comm2_7reverseRows e0Rows = comm2_7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_8left : packedMul e2Rows e8Rows = comm2_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_8reverse : packedMul e8Rows e2Rows = comm2_8reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_8right : packedMul comm2_8reverseRows e0Rows = comm2_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_9left : packedMul e2Rows e9Rows = comm2_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
