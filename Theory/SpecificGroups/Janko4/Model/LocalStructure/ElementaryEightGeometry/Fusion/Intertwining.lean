module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Fusion.Products5

/-!
# Intertwining equations for the native fusion conjugator

These equations keep the literal lifts and the original kernel masks. They
are checked before transporting them through the faithful representation.
-/

public section
namespace Janko4.LocalStructure.ElementaryEightGeometry.FusionMatrices
open Janko4.GeneratorCertificates Janko4.Cardinality.KernelCount
open Janko4.LocalStructure.ElementaryEightGeometry.LiftMatrices
set_option maxRecDepth 10000
set_option Elab.async false
set_option maxHeartbeats 800000 in
theorem intertwine_lift_0 : packedMul conjugatorRows l0Rows = packedMul t0_2Rows conjugatorRows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem intertwine_lift_1 : packedMul conjugatorRows l1Rows = packedMul t1_2Rows conjugatorRows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem intertwine_lift_2 : packedMul conjugatorRows l2Rows = packedMul t2_1Rows conjugatorRows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem intertwine_lift_3 : packedMul conjugatorRows l5Rows = packedMul t3_3Rows conjugatorRows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem intertwine_mask_1 : packedMul conjugatorRows e0Rows = packedMul e0Rows conjugatorRows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem intertwine_mask_2 : packedMul conjugatorRows e1Rows = packedMul m822Rows conjugatorRows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem intertwine_mask_816 : packedMul conjugatorRows m816Rows = packedMul m1128Rows conjugatorRows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem intertwine_mask_1128 : packedMul conjugatorRows m1128Rows = packedMul e2Rows conjugatorRows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
end Janko4.LocalStructure.ElementaryEightGeometry.FusionMatrices
