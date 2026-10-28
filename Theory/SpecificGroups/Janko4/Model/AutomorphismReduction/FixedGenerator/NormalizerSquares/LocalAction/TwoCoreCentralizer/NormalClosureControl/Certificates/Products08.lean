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

theorem product_comm5_10reverse : packedMul e10Rows e5Rows = comm5_10reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_10right : packedMul comm5_10reverseRows e0Rows = comm5_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_11left : packedMul e5Rows e11Rows = comm5_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_11right : packedMul e11Rows e5Rows = comm5_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_12left : packedMul e5Rows e12Rows = comm5_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm5_12right : packedMul e12Rows e5Rows = comm5_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_7left : packedMul e6Rows e7Rows = comm6_7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_7right : packedMul e7Rows e6Rows = comm6_7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_8left : packedMul e6Rows e8Rows = comm6_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_8reverse : packedMul e8Rows e6Rows = comm6_8reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_8right : packedMul comm6_8reverseRows e0Rows = comm6_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_9left : packedMul e6Rows e9Rows = comm6_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_9reverse : packedMul e9Rows e6Rows = comm6_9reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_9right : packedMul comm6_9reverseRows e0Rows = comm6_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_10left : packedMul e6Rows e10Rows = comm6_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_10right : packedMul e10Rows e6Rows = comm6_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
