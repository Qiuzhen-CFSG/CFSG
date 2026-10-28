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

theorem product_comm1_6reverse : packedMul e6Rows e1Rows = comm1_6reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_6right : packedMul comm1_6reverseRows e0Rows = comm1_6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_7left : packedMul e1Rows e7Rows = comm1_7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_7right : packedMul e7Rows e1Rows = comm1_7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_8left : packedMul e1Rows e8Rows = comm1_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_8reverse : packedMul e8Rows e1Rows = comm1_8reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_8right : packedMul comm1_8reverseRows e0Rows = comm1_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_9left : packedMul e1Rows e9Rows = comm1_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_9right : packedMul e9Rows e1Rows = comm1_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_10left : packedMul e1Rows e10Rows = comm1_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_10reverse : packedMul e10Rows e1Rows = comm1_10reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_10right : packedMul comm1_10reverseRows e0Rows = comm1_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_11left : packedMul e1Rows e11Rows = comm1_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_11right : packedMul e11Rows e1Rows = comm1_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_12left : packedMul e1Rows e12Rows = comm1_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm1_12reverse : packedMul e12Rows e1Rows = comm1_12reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
