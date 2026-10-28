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
theorem action_x_6_right : packedMul product_stage17Rows e6Rows = action_x_6_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_7_left : packedMul e7Rows product_stage17Rows = action_x_7_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_7_right : packedMul product_stage17Rows e7Rows = action_x_7_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_1_left : packedMul seedPower6Rows product_stage14Rows = action_y_1_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_1_right : packedMul product_stage14Rows e2Rows = action_y_1_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_2_left : packedMul e2Rows product_stage14Rows = action_y_2_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_2_right : packedMul product_stage14Rows e4Rows = action_y_2_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_3_left : packedMul e3Rows product_stage14Rows = action_y_3_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_3_right : packedMul product_stage14Rows e3Rows = action_y_3_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_4_left : packedMul e4Rows product_stage14Rows = action_y_4_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_4_right : packedMul product_stage14Rows e6Rows = action_y_4_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_5_left : packedMul e5Rows product_stage14Rows = action_y_5_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_5_right : packedMul product_stage14Rows e7Rows = action_y_5_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_6_left : packedMul e6Rows product_stage14Rows = action_y_6_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_6_right : packedMul product_stage14Rows seedPower6Rows = action_y_6_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_y_7_left : packedMul e7Rows product_stage14Rows = action_y_7_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalEight
