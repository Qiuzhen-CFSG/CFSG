module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Products2

/-!
# Checked native matrix products

This bounded batch certifies the literal word DAG using packed XOR arithmetic.
`decode_packedMul` identifies every certificate with ordinary binary matrix
multiplication. Evaluation in the native subgroup is a separate theorem.
-/

public section
namespace Janko4.LocalStructure.LinearFive
open Janko4.GeneratorCertificates Janko4.Cardinality.KernelCount
namespace NativeRows
set_option maxRecDepth 10000
set_option Elab.async false
set_option maxHeartbeats 800000 in
theorem product_p2_0 : packedMul d8Rows d6Rows = p2_0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_1 : packedMul p2_0Rows d42Rows = p2_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_2 : packedMul p2_1Rows d8Rows = p2_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_3 : packedMul p2_2Rows d7Rows = p2_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_4 : packedMul p2_3Rows d44Rows = p2_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_5 : packedMul p2_4Rows d3Rows = p2_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_6 : packedMul p2_5Rows d30Rows = p2_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_7 : packedMul p2_6Rows d22Rows = p2_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_8 : packedMul p2_7Rows d45Rows = p2_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_9 : packedMul p2_8Rows d7Rows = p2_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_10 : packedMul p2_9Rows d24Rows = p2_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_11 : packedMul p2_10Rows d9Rows = p2_11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_12 : packedMul p2_11Rows d9Rows = p2_12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_13 : packedMul p2_12Rows d9Rows = p2_13Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_14 : packedMul p2_13Rows iyRows = p2_14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_15 : packedMul p2_14Rows d17Rows = p2_15Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_16 : packedMul p2_15Rows d20Rows = p2_16Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_17 : packedMul p2_16Rows d38Rows = p2_17Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_18 : packedMul p2_17Rows d12Rows = p2_18Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_19 : packedMul p2_18Rows d9Rows = p2_19Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_20 : packedMul p2_19Rows d28Rows = p2_20Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_21 : packedMul p2_20Rows d6Rows = p2_21Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_22 : packedMul p2_21Rows d15Rows = p2_22Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p2_23 : packedMul p2_22Rows d43Rows = p2_23Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end NativeRows
end Janko4.LocalStructure.LinearFive
