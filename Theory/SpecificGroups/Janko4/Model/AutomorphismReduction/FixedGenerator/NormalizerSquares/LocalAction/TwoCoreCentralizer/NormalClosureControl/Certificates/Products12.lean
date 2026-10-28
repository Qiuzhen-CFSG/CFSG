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

theorem product_mask2171_3 : packedMul e3Rows mask2171_4Rows = mask2171_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask2171_1 : packedMul e1Rows mask2171_3Rows = mask2171_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask2171_0 : packedMul e0Rows mask2171_1Rows = mask2171_0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask5964_10 : packedMul e10Rows e12Rows = mask5964_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask5964_9 : packedMul e9Rows mask5964_10Rows = mask5964_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask5964_8 : packedMul e8Rows mask5964_9Rows = mask5964_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask5964_6 : packedMul e6Rows mask5964_8Rows = mask5964_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask5964_3 : packedMul e3Rows mask5964_6Rows = mask5964_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask5964_2 : packedMul e2Rows mask5964_3Rows = mask5964_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask6046_10 : packedMul e10Rows e12Rows = mask6046_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask6046_9 : packedMul e9Rows mask6046_10Rows = mask6046_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask6046_8 : packedMul e8Rows mask6046_9Rows = mask6046_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask6046_7 : packedMul e7Rows mask6046_8Rows = mask6046_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask6046_4 : packedMul e4Rows mask6046_7Rows = mask6046_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask6046_3 : packedMul e3Rows mask6046_4Rows = mask6046_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_mask6046_2 : packedMul e2Rows mask6046_3Rows = mask6046_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
