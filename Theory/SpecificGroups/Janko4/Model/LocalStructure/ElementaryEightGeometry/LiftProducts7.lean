module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftProducts6

/-!
# Checked products for the native lift words

Each packed equality is checked by Lean and denotes ordinary binary matrix
multiplication. Sequential batches bound simultaneous certificate memory.
-/

public section
namespace Janko4.LocalStructure.ElementaryEightGeometry.LiftMatrices
open Janko4.GeneratorCertificates Janko4.Cardinality.KernelCount
set_option maxRecDepth 10000
set_option Elab.async false
set_option maxHeartbeats 800000 in
theorem product_w171 : packedMul w170Rows w9Rows = w171Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w172 : packedMul w171Rows w63Rows = w172Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w173 : packedMul w172Rows w7Rows = w173Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w174 : packedMul w173Rows w15Rows = w174Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w175 : packedMul w174Rows w25Rows = w175Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w176 : packedMul w175Rows inverseYRows = w176Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w177 : packedMul w176Rows w65Rows = w177Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w178 : packedMul w40Rows w20Rows = w178Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w179 : packedMul w178Rows w15Rows = w179Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w180 : packedMul w179Rows w62Rows = w180Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w181 : packedMul w180Rows w8Rows = w181Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w182 : packedMul w181Rows w17Rows = w182Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w183 : packedMul w182Rows w34Rows = w183Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w184 : packedMul w183Rows w12Rows = w184Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w185 : packedMul w184Rows w23Rows = w185Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w186 : packedMul w185Rows w12Rows = w186Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w187 : packedMul w186Rows w8Rows = w187Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w188 : packedMul w187Rows w47Rows = w188Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w189 : packedMul w188Rows w17Rows = w189Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w190 : packedMul w189Rows w58Rows = w190Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w191 : packedMul w190Rows xRows = w191Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w192 : packedMul w191Rows w60Rows = w192Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w193 : packedMul w192Rows w17Rows = w193Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w194 : packedMul w193Rows w42Rows = w194Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryEightGeometry.LiftMatrices
