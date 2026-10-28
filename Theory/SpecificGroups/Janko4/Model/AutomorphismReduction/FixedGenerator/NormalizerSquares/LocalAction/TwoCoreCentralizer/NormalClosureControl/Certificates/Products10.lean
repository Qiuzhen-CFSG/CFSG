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

theorem product_comm7_12right : packedMul e12Rows e7Rows = comm7_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_9left : packedMul e8Rows e9Rows = comm8_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_9right : packedMul e9Rows e8Rows = comm8_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_10left : packedMul e8Rows e10Rows = comm8_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_10reverse : packedMul e10Rows e8Rows = comm8_10reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_10right : packedMul comm8_10reverseRows e0Rows = comm8_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_11left : packedMul e8Rows e11Rows = comm8_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_11reverse : packedMul e11Rows e8Rows = comm8_11reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_11right : packedMul comm8_11reverseRows e0Rows = comm8_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_12left : packedMul e8Rows e12Rows = comm8_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_12reverse : packedMul e12Rows e8Rows = comm8_12reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm8_12right : packedMul comm8_12reverseRows e0Rows = comm8_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_10left : packedMul e9Rows e10Rows = comm9_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_10reverse : packedMul e10Rows e9Rows = comm9_10reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_10right : packedMul comm9_10reverseRows e0Rows = comm9_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_11left : packedMul e9Rows e11Rows = comm9_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
