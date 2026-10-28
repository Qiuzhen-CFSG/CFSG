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

theorem product_word2left : packedMul e1Rows yRows = word2leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word2right : packedMul yRows e2Rows = word2leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word3left : packedMul e2Rows yRows = word3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word3right : packedMul yRows e3Rows = word3leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word4left : packedMul e3Rows xRows = word4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word4right : packedMul xRows e4Rows = word4leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word5left : packedMul e4Rows yRows = word5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word5right : packedMul yRows e5Rows = word5leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word6left : packedMul e5Rows xRows = word6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word6right : packedMul xRows e6Rows = word6leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word7left : packedMul e5Rows yRows = word7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word7right : packedMul yRows e7Rows = word7leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word8left : packedMul e6Rows yRows = word8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word8right : packedMul yRows e8Rows = word8leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word9left : packedMul e7Rows xRows = word9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

theorem product_word9right : packedMul xRows e9Rows = word9leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.Certificates
