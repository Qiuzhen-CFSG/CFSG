module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Fusion.Products3

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
theorem product_t0_2 : packedMul t0_1Rows l4Rows = t0_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m3 : packedMul e0Rows e1Rows = m3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m7 : packedMul m3Rows e2Rows = m7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m23 : packedMul m7Rows e4Rows = m23Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m55 : packedMul m23Rows e5Rows = m55Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m311 : packedMul m55Rows e8Rows = m311Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m823 : packedMul m311Rows e9Rows = m823Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_t1_0 : packedMul m823Rows l0Rows = t1_0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_t1_2 : packedMul t1_0Rows l4Rows = t1_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m6 : packedMul e1Rows e2Rows = m6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m14 : packedMul m6Rows e3Rows = m14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m30 : packedMul m14Rows e4Rows = m30Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m94 : packedMul m30Rows e6Rows = m94Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m350 : packedMul m94Rows e8Rows = m350Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m862 : packedMul m350Rows e9Rows = m862Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m1886 : packedMul m862Rows e10Rows = m1886Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_t2_1 : packedMul m1886Rows l3Rows = t2_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m22 : packedMul m6Rows e4Rows = m22Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m54 : packedMul m22Rows e5Rows = m54Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m310 : packedMul m54Rows e8Rows = m310Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryEightGeometry.FusionMatrices
