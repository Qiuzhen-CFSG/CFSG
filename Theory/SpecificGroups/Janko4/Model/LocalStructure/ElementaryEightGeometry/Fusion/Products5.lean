module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Fusion.Products4

/-!
# Checked native fusion products

Each certificate is kernel-checked and denotes ordinary matrix multiplication.
The import chain bounds simultaneous certificate elaboration.
-/

public section
namespace Janko4.LocalStructure.ElementaryEightGeometry.FusionMatrices
open Janko4.GeneratorCertificates Janko4.Cardinality.KernelCount
open Janko4.LocalStructure.ElementaryEightGeometry.LiftMatrices
set_option maxRecDepth 10000
set_option Elab.async false
set_option maxHeartbeats 800000 in
theorem product_m822 : packedMul m310Rows e9Rows = m822Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_t3_0 : packedMul m822Rows l0Rows = t3_0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_t3_3 : packedMul t3_0Rows l5Rows = t3_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m48 : packedMul e4Rows e5Rows = m48Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m304 : packedMul m48Rows e8Rows = m304Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m816 : packedMul m304Rows e9Rows = m816Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m40 : packedMul e3Rows e5Rows = m40Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m104 : packedMul m40Rows e6Rows = m104Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m1128 : packedMul m104Rows e10Rows = m1128Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryEightGeometry.FusionMatrices
