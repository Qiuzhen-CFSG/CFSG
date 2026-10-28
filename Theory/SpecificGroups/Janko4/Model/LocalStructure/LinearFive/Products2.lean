module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Products1

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
theorem product_p1_0 : packedMul d23Rows d38Rows = p1_0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_1 : packedMul p1_0Rows d7Rows = p1_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_2 : packedMul p1_1Rows d39Rows = p1_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_3 : packedMul p1_2Rows d40Rows = p1_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_4 : packedMul p1_3Rows d7Rows = p1_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_5 : packedMul p1_4Rows d41Rows = p1_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_6 : packedMul p1_5Rows xRows = p1_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_7 : packedMul p1_6Rows d4Rows = p1_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_8 : packedMul p1_7Rows d24Rows = p1_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_9 : packedMul p1_8Rows yRows = p1_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_10 : packedMul p1_9Rows d15Rows = p1_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_11 : packedMul p1_10Rows d28Rows = p1_11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_12 : packedMul p1_11Rows d9Rows = p1_12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_13 : packedMul p1_12Rows d15Rows = p1_13Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_14 : packedMul p1_13Rows d5Rows = p1_14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_15 : packedMul p1_14Rows d14Rows = p1_15Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_16 : packedMul p1_15Rows d25Rows = p1_16Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_17 : packedMul p1_16Rows d20Rows = p1_17Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_18 : packedMul p1_17Rows d6Rows = p1_18Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_19 : packedMul p1_18Rows d5Rows = p1_19Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_20 : packedMul p1_19Rows d31Rows = p1_20Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_21 : packedMul p1_20Rows d3Rows = p1_21Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_22 : packedMul p1_21Rows d25Rows = p1_22Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_23 : packedMul p1_22Rows d9Rows = p1_23Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_24 : packedMul p1_23Rows d42Rows = p1_24Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_25 : packedMul p1_24Rows d20Rows = p1_25Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_26 : packedMul p1_25Rows d13Rows = p1_26Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_27 : packedMul p1_26Rows d5Rows = p1_27Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_28 : packedMul p1_27Rows yRows = p1_28Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_29 : packedMul p1_28Rows d7Rows = p1_29Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_30 : packedMul p1_29Rows d4Rows = p1_30Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_31 : packedMul p1_30Rows d4Rows = p1_31Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_32 : packedMul p1_31Rows d43Rows = p1_32Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_33 : packedMul p1_32Rows d15Rows = p1_33Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_34 : packedMul p1_33Rows d20Rows = p1_34Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p1_35 : packedMul p1_34Rows d17Rows = p1_35Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end NativeRows
end Janko4.LocalStructure.LinearFive
