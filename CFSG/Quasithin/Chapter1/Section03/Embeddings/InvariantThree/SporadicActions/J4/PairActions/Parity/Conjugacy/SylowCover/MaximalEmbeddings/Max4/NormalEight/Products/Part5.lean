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
theorem mul_5_1 : packedMul e5Rows seedPower6Rows = e2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_5_2 : packedMul e5Rows e2Rows = seedPower6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_5_3 : packedMul e5Rows e3Rows = e7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_5_4 : packedMul e5Rows e4Rows = e6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_5_5 : packedMul e5Rows e5Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_5_6 : packedMul e5Rows e6Rows = e4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_5_7 : packedMul e5Rows e7Rows = e3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_6_1 : packedMul e6Rows seedPower6Rows = e7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_6_2 : packedMul e6Rows e2Rows = e3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_6_3 : packedMul e6Rows e3Rows = e2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_6_4 : packedMul e6Rows e4Rows = e5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_6_5 : packedMul e6Rows e5Rows = e4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_6_6 : packedMul e6Rows e6Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_6_7 : packedMul e6Rows e7Rows = seedPower6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_7_1 : packedMul e7Rows seedPower6Rows = e6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem mul_7_2 : packedMul e7Rows e2Rows = e4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalEight
