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

theorem product_comm9_11right : packedMul e11Rows e9Rows = comm9_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_12left : packedMul e9Rows e12Rows = comm9_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm9_12right : packedMul e12Rows e9Rows = comm9_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_11left : packedMul e10Rows e11Rows = comm10_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_11reverse : packedMul e11Rows e10Rows = comm10_11reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_11right : packedMul comm10_11reverseRows e0Rows = comm10_11leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_12left : packedMul e10Rows e12Rows = comm10_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_12reverse : packedMul e12Rows e10Rows = comm10_12reverseRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm10_12right : packedMul comm10_12reverseRows e0Rows = comm10_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm11_12left : packedMul e11Rows e12Rows = comm11_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_comm11_12right : packedMul e12Rows e11Rows = comm11_12leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask3_0 : packedMul e0Rows e1Rows = mask3_0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask5_0 : packedMul e0Rows e2Rows = mask5_0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask2171_6 : packedMul e6Rows e11Rows = mask2171_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask2171_5 : packedMul e5Rows mask2171_6Rows = mask2171_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask2171_4 : packedMul e4Rows mask2171_5Rows = mask2171_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
