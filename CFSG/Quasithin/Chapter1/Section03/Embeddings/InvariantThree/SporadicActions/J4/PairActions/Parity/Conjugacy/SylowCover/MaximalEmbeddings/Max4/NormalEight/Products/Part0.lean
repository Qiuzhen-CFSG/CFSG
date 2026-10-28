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
theorem product_stage01 : packedMul aRows bRows = product_stage01Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage02Power2 : packedMul product_stage01Rows product_stage01Rows = stage02Power2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage02Power3 : packedMul stage02Power2Rows product_stage01Rows = stage02Power3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage03 : packedMul stage02Power3Rows bRows = product_stage03Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage04 : packedMul bRows aRows = product_stage04Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage05 : packedMul product_stage03Rows bRows = product_stage05Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage06Power2 : packedMul product_stage05Rows product_stage05Rows = stage06Power2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage06Power3 : packedMul stage06Power2Rows product_stage05Rows = stage06Power3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage07Power2 : packedMul product_stage04Rows product_stage04Rows = stage07Power2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage07Power4 : packedMul stage07Power2Rows stage07Power2Rows = stage07Power4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage07Power5 : packedMul stage07Power4Rows product_stage04Rows = stage07Power5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage07Power10 : packedMul stage07Power5Rows stage07Power5Rows = stage07Power10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage07Power11 : packedMul stage07Power10Rows product_stage04Rows = stage07Power11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage07Power22 : packedMul stage07Power11Rows stage07Power11Rows = stage07Power22Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage08Power6 : packedMul stage02Power3Rows stage02Power3Rows = stage08Power6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem stage08Power12 : packedMul stage08Power6Rows stage08Power6Rows = stage08Power12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalEight
