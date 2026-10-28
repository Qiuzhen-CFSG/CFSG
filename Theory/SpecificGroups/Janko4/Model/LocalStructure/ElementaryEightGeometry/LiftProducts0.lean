module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftMatrices

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
theorem product_inverseY : packedMul yRows inverseYRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w4 : packedMul xRows yRows = w4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w5 : packedMul xRows inverseYRows = w5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w6 : packedMul xRows inverseYRows = w6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w7 : packedMul xRows yRows = w7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w8 : packedMul w4Rows w4Rows = w8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w9 : packedMul w5Rows w5Rows = w9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w10 : packedMul w7Rows w6Rows = w10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w11 : packedMul w6Rows w6Rows = w11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w12 : packedMul w5Rows w8Rows = w12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w13 : packedMul w7Rows w7Rows = w13Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w14 : packedMul w4Rows w9Rows = w14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w15 : packedMul w10Rows w10Rows = w15Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w16 : packedMul w5Rows w14Rows = w16Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w17 : packedMul w4Rows w12Rows = w17Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w18 : packedMul w10Rows w7Rows = w18Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w19 : packedMul w17Rows w8Rows = w19Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w20 : packedMul w11Rows w6Rows = w20Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w21 : packedMul w14Rows w12Rows = w21Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w22 : packedMul w10Rows w6Rows = w22Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w23 : packedMul w13Rows w13Rows = w23Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w24 : packedMul w5Rows w4Rows = w24Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w25 : packedMul w11Rows w11Rows = w25Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w26 : packedMul w18Rows w18Rows = w26Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryEightGeometry.LiftMatrices
