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

theorem product_comm3_6reverse : packedMul e6Rows e3Rows = comm3_6reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_6right : packedMul comm3_6reverseRows e0Rows = comm3_6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_7left : packedMul e3Rows e7Rows = comm3_7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_7right : packedMul e7Rows e3Rows = comm3_7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_8left : packedMul e3Rows e8Rows = comm3_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_8right : packedMul e8Rows e3Rows = comm3_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_9left : packedMul e3Rows e9Rows = comm3_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_9reverse : packedMul e9Rows e3Rows = comm3_9reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_9right : packedMul comm3_9reverseRows e0Rows = comm3_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_10left : packedMul e3Rows e10Rows = comm3_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_10right : packedMul e10Rows e3Rows = comm3_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_11left : packedMul e3Rows e11Rows = comm3_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_11reverse : packedMul e11Rows e3Rows = comm3_11reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_11right : packedMul comm3_11reverseRows e0Rows = comm3_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_12left : packedMul e3Rows e12Rows = comm3_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_12reverse : packedMul e12Rows e3Rows = comm3_12reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
