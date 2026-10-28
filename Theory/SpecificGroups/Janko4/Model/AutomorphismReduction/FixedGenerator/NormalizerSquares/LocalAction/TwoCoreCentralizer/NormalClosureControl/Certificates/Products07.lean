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

theorem product_comm4_11reverse : packedMul e11Rows e4Rows = comm4_11reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_11right : packedMul comm4_11reverseRows e0Rows = comm4_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_12left : packedMul e4Rows e12Rows = comm4_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_12reverse : packedMul e12Rows e4Rows = comm4_12reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_12right : packedMul comm4_12reverseRows e0Rows = comm4_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_6left : packedMul e5Rows e6Rows = comm5_6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_6reverse : packedMul e6Rows e5Rows = comm5_6reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_6right : packedMul comm5_6reverseRows e0Rows = comm5_6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_7left : packedMul e5Rows e7Rows = comm5_7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_7reverse : packedMul e7Rows e5Rows = comm5_7reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_7right : packedMul comm5_7reverseRows e0Rows = comm5_7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_8left : packedMul e5Rows e8Rows = comm5_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_8right : packedMul e8Rows e5Rows = comm5_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_9left : packedMul e5Rows e9Rows = comm5_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_9right : packedMul e9Rows e5Rows = comm5_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_10left : packedMul e5Rows e10Rows = comm5_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
