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

theorem product_comm3_12right : packedMul comm3_12reverseRows e0Rows = comm3_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_5left : packedMul e4Rows e5Rows = comm4_5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_5reverse : packedMul e5Rows e4Rows = comm4_5reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_5right : packedMul comm4_5reverseRows e0Rows = comm4_5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_6left : packedMul e4Rows e6Rows = comm4_6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_6right : packedMul e6Rows e4Rows = comm4_6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_7left : packedMul e4Rows e7Rows = comm4_7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_7reverse : packedMul e7Rows e4Rows = comm4_7reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_7right : packedMul comm4_7reverseRows e0Rows = comm4_7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_8left : packedMul e4Rows e8Rows = comm4_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_8right : packedMul e8Rows e4Rows = comm4_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_9left : packedMul e4Rows e9Rows = comm4_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_9right : packedMul e9Rows e4Rows = comm4_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_10left : packedMul e4Rows e10Rows = comm4_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_10right : packedMul e10Rows e4Rows = comm4_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm4_11left : packedMul e4Rows e11Rows = comm4_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
