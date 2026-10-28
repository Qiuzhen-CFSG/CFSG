module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Products0

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
theorem product_p0_0 : packedMul d23Rows d6Rows = p0_0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_1 : packedMul p0_0Rows d13Rows = p0_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_2 : packedMul p0_1Rows d15Rows = p0_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_3 : packedMul p0_2Rows d13Rows = p0_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_4 : packedMul p0_3Rows d12Rows = p0_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_5 : packedMul p0_4Rows d29Rows = p0_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_6 : packedMul p0_5Rows d18Rows = p0_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_7 : packedMul p0_6Rows d3Rows = p0_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_8 : packedMul p0_7Rows d10Rows = p0_8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_9 : packedMul p0_8Rows d11Rows = p0_9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_10 : packedMul p0_9Rows d7Rows = p0_10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_11 : packedMul p0_10Rows d19Rows = p0_11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_12 : packedMul p0_11Rows d19Rows = p0_12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_13 : packedMul p0_12Rows d30Rows = p0_13Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_14 : packedMul p0_13Rows d16Rows = p0_14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_15 : packedMul p0_14Rows d31Rows = p0_15Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_16 : packedMul p0_15Rows d24Rows = p0_16Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_17 : packedMul p0_16Rows d25Rows = p0_17Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_18 : packedMul p0_17Rows d17Rows = p0_18Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_19 : packedMul p0_18Rows d26Rows = p0_19Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_20 : packedMul p0_19Rows d27Rows = p0_20Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_21 : packedMul p0_20Rows d10Rows = p0_21Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_p0_22 : packedMul p0_21Rows d37Rows = p0_22Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end NativeRows
end Janko4.LocalStructure.LinearFive
