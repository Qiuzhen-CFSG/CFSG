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

theorem product_comm6_11left : packedMul e6Rows e11Rows = comm6_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_11reverse : packedMul e11Rows e6Rows = comm6_11reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_11right : packedMul comm6_11reverseRows e0Rows = comm6_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_12left : packedMul e6Rows e12Rows = comm6_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm6_12right : packedMul e12Rows e6Rows = comm6_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_8left : packedMul e7Rows e8Rows = comm7_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_8reverse : packedMul e8Rows e7Rows = comm7_8reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_8right : packedMul comm7_8reverseRows e0Rows = comm7_8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_9left : packedMul e7Rows e9Rows = comm7_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_9reverse : packedMul e9Rows e7Rows = comm7_9reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_9right : packedMul comm7_9reverseRows e0Rows = comm7_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_10left : packedMul e7Rows e10Rows = comm7_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_10right : packedMul e10Rows e7Rows = comm7_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_11left : packedMul e7Rows e11Rows = comm7_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_11right : packedMul e11Rows e7Rows = comm7_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm7_12left : packedMul e7Rows e12Rows = comm7_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
