module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftProducts7

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
theorem product_w195 : packedMul w194Rows w11Rows = w195Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w196 : packedMul w195Rows w13Rows = w196Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w197 : packedMul w196Rows w33Rows = w197Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w198 : packedMul w197Rows w14Rows = w198Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w199 : packedMul w198Rows w43Rows = w199Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w200 : packedMul w199Rows xRows = w200Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w201 : packedMul w200Rows w65Rows = w201Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k192 : packedMul e6Rows e7Rows = k192Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k448 : packedMul k192Rows e8Rows = k448Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k1472 : packedMul k448Rows e10Rows = k1472Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_l0 : packedMul k1472Rows w88Rows = l0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k544 : packedMul e5Rows e9Rows = k544Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_l1 : packedMul k544Rows w105Rows = l1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k36 : packedMul e2Rows e5Rows = k36Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k100 : packedMul k36Rows e6Rows = k100Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k228 : packedMul k100Rows e7Rows = k228Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k740 : packedMul k228Rows e9Rows = k740Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k1764 : packedMul k740Rows e10Rows = k1764Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_l2 : packedMul k1764Rows w125Rows = l2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k288 : packedMul e5Rows e8Rows = k288Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k800 : packedMul k288Rows e9Rows = k800Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k1824 : packedMul k800Rows e10Rows = k1824Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_l3 : packedMul k1824Rows w157Rows = l3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k160 : packedMul e5Rows e7Rows = k160Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryEightGeometry.LiftMatrices
