module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Products4

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
theorem product_k5 : packedMul e0Rows e2Rows = k5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k13 : packedMul k5Rows e3Rows = k13Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k6 : packedMul e1Rows e2Rows = k6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k22 : packedMul k6Rows e4Rows = k22Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k3 : packedMul e0Rows e1Rows = k3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k7 : packedMul k3Rows e2Rows = k7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k15 : packedMul k7Rows e3Rows = k15Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k19 : packedMul k3Rows e4Rows = k19Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k51 : packedMul k19Rows e5Rows = k51Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k9 : packedMul e0Rows e3Rows = k9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k73 : packedMul k9Rows e6Rows = k73Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k12 : packedMul e2Rows e3Rows = k12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k140 : packedMul k12Rows e7Rows = k140Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k25 : packedMul k9Rows e4Rows = k25Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k281 : packedMul k25Rows e8Rows = k281Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k515 : packedMul k3Rows e9Rows = k515Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k17 : packedMul e0Rows e4Rows = k17Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k1041 : packedMul k17Rows e10Rows = k1041Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f0 : packedMul p0_22Rows k13Rows = f0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f1 : packedMul p1_35Rows k13Rows = f1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f2 : packedMul p2_23Rows k22Rows = f2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f3 : packedMul p3_21Rows k15Rows = f3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end NativeRows
end Janko4.LocalStructure.LinearFive
