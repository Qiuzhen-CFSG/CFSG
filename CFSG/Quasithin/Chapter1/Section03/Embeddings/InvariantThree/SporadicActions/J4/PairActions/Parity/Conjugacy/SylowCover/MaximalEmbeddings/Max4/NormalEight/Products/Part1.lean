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
theorem stage08Power13 : packedMul stage08Power12Rows product_stage01Rows = stage08Power13Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage09 : packedMul stage07Power22Rows stage08Power13Rows = product_stage09Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage10 : packedMul product_stage04Rows product_stage04Rows = product_stage10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage11 : packedMul stage11Rows product_stage09Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage12 : packedMul stage11Rows stage06Power3Rows = product_stage12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage13 : packedMul stage06Power3Rows stage06Power3Rows = product_stage13Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage14 : packedMul product_stage12Rows product_stage09Rows = product_stage14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage15 : packedMul stage15Rows product_stage10Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage16 : packedMul stage15Rows product_stage13Rows = product_stage16Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_stage17 : packedMul product_stage16Rows product_stage10Rows = product_stage17Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem x_inverse : packedMul product_stage17Rows xInverseRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem y_inverse : packedMul product_stage14Rows yInverseRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem word1 : packedMul xInverseRows product_stage14Rows = word1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word2 : packedMul word1Rows product_stage17Rows = word2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word3 : packedMul word2Rows product_stage17Rows = word3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word4 : packedMul word3Rows product_stage17Rows = word4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)


end Janko4.LocalStructure.SymmetricLinear.NormalEight
