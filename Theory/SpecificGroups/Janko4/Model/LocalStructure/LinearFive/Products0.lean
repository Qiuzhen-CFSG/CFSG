module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Rows

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
theorem inverse_y : packedMul yRows iyRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d3 : packedMul xRows yRows = d3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d4 : packedMul xRows iyRows = d4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d5 : packedMul xRows yRows = d5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d6 : packedMul xRows iyRows = d6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d7 : packedMul d4Rows d3Rows = d7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d8 : packedMul d5Rows d5Rows = d8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d9 : packedMul d6Rows d6Rows = d9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d10 : packedMul d4Rows d7Rows = d10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d11 : packedMul d3Rows d3Rows = d11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d12 : packedMul d4Rows d10Rows = d12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d13 : packedMul d5Rows d6Rows = d13Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d14 : packedMul d3Rows d7Rows = d14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d15 : packedMul d5Rows d9Rows = d15Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d16 : packedMul d7Rows d11Rows = d16Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d17 : packedMul d13Rows d8Rows = d17Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d18 : packedMul d10Rows d14Rows = d18Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d19 : packedMul d4Rows d12Rows = d19Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d20 : packedMul d6Rows d8Rows = d20Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d21 : packedMul d3Rows d12Rows = d21Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d22 : packedMul d7Rows d14Rows = d22Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d23 : packedMul d8Rows d8Rows = d23Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d24 : packedMul d4Rows d19Rows = d24Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d25 : packedMul d4Rows iyRows = d25Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d26 : packedMul d13Rows iyRows = d26Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d27 : packedMul d11Rows d16Rows = d27Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d28 : packedMul d9Rows d8Rows = d28Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d29 : packedMul d7Rows d10Rows = d29Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d30 : packedMul d4Rows xRows = d30Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d31 : packedMul d11Rows d21Rows = d31Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d32 : packedMul d12Rows d27Rows = d32Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d33 : packedMul d32Rows d3Rows = d33Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d34 : packedMul d33Rows d13Rows = d34Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d35 : packedMul d34Rows d26Rows = d35Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d36 : packedMul d35Rows d21Rows = d36Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d37 : packedMul d36Rows d11Rows = d37Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d38 : packedMul d8Rows yRows = d38Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d39 : packedMul d7Rows d12Rows = d39Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d40 : packedMul d3Rows xRows = d40Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d41 : packedMul d22Rows d11Rows = d41Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d42 : packedMul d17Rows d15Rows = d42Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d43 : packedMul d9Rows d6Rows = d43Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d44 : packedMul d18Rows d10Rows = d44Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_d45 : packedMul d16Rows d14Rows = d45Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end NativeRows
end Janko4.LocalStructure.LinearFive
