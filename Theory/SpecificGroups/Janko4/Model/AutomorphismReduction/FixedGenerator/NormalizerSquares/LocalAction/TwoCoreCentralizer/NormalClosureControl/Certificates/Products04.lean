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

theorem product_comm2_9reverse : packedMul e9Rows e2Rows = comm2_9reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_9right : packedMul comm2_9reverseRows e0Rows = comm2_9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_10left : packedMul e2Rows e10Rows = comm2_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_10reverse : packedMul e10Rows e2Rows = comm2_10reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_10right : packedMul comm2_10reverseRows e0Rows = comm2_10leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_11left : packedMul e2Rows e11Rows = comm2_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_11reverse : packedMul e11Rows e2Rows = comm2_11reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_11right : packedMul comm2_11reverseRows e0Rows = comm2_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_12left : packedMul e2Rows e12Rows = comm2_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm2_12right : packedMul e12Rows e2Rows = comm2_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_4left : packedMul e3Rows e4Rows = comm3_4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_4reverse : packedMul e4Rows e3Rows = comm3_4reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_4right : packedMul comm3_4reverseRows e0Rows = comm3_4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_5left : packedMul e3Rows e5Rows = comm3_5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_5right : packedMul e5Rows e3Rows = comm3_5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm3_6left : packedMul e3Rows e6Rows = comm3_6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
