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
theorem mul_7_3 : packedMul e7Rows e3Rows = e5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_7_4 : packedMul e7Rows e4Rows = e2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_7_5 : packedMul e7Rows e5Rows = e3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_7_6 : packedMul e7Rows e6Rows = seedPower6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_7_7 : packedMul e7Rows e7Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_1_left : packedMul seedPower6Rows product_stage17Rows = action_x_1_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_1_right : packedMul product_stage17Rows seedPower6Rows = action_x_1_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_2_left : packedMul e2Rows product_stage17Rows = action_x_2_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_2_right : packedMul product_stage17Rows e3Rows = action_x_2_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_3_left : packedMul e3Rows product_stage17Rows = action_x_3_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_3_right : packedMul product_stage17Rows e2Rows = action_x_3_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_4_left : packedMul e4Rows product_stage17Rows = action_x_4_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_4_right : packedMul product_stage17Rows e5Rows = action_x_4_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_5_left : packedMul e5Rows product_stage17Rows = action_x_5_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_5_right : packedMul product_stage17Rows e4Rows = action_x_5_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem action_x_6_left : packedMul e6Rows product_stage17Rows = action_x_6_leftRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalEight
