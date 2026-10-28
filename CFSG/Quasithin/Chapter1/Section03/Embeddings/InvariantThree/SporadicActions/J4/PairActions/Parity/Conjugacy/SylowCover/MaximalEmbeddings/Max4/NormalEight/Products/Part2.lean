module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Data

/-! Kernel-checked packed products for the literal max4 normal eight.
See Data and source/generate.py for the ATLAS source and witness generation.
Sequential declaration checking bounds memory during the XOR reductions. -/

public section

namespace Janko4.LocalStructure.SymmetricLinear.NormalEight
open Janko4.GeneratorCertificates

set_option Elab.async false

set_option maxRecDepth 10000 in
theorem word5 : packedMul word4Rows yInverseRows = word5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word6 : packedMul word5Rows xInverseRows = word6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word7 : packedMul word6Rows yInverseRows = word7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word8 : packedMul word7Rows xInverseRows = word8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word9 : packedMul word8Rows xInverseRows = word9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem seedPower2 : packedMul word9Rows word9Rows = seedPower2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem seedPower3 : packedMul seedPower2Rows word9Rows = seedPower3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem seedPower6 : packedMul seedPower3Rows seedPower3Rows = seedPower6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem orbit2_left : packedMul seedPower6Rows product_stage14Rows = orbit2_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem orbit2_right : packedMul product_stage14Rows e2Rows = orbit2_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem orbit3_left : packedMul e2Rows product_stage17Rows = orbit3_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem orbit3_right : packedMul product_stage17Rows e3Rows = orbit3_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem orbit4_left : packedMul e2Rows product_stage14Rows = orbit4_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem orbit4_right : packedMul product_stage14Rows e4Rows = orbit4_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem orbit5_left : packedMul e4Rows product_stage17Rows = orbit5_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem orbit5_right : packedMul product_stage17Rows e5Rows = orbit5_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalEight
