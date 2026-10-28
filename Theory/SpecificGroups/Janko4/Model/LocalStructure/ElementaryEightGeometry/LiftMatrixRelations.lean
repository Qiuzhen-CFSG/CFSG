module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftProducts9

/-!
# Native lift squares and commutators

The two rows, including their shared Figure 1 pair representative, are commuting
involutions after their checked kernel corrections. No relation is assumed.
-/

public section
namespace Janko4.LocalStructure.ElementaryEightGeometry.LiftMatrices
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
set_option maxHeartbeats 800000 in
theorem square_0 : packedMul l0Rows l0Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem square_1 : packedMul l1Rows l1Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem square_2 : packedMul l2Rows l2Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem square_3 : packedMul l3Rows l3Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem square_4 : packedMul l4Rows l4Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem square_5 : packedMul l5Rows l5Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem commute_0_1 : packedMul l0Rows l1Rows = packedMul l1Rows l0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem commute_0_2 : packedMul l0Rows l2Rows = packedMul l2Rows l0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem commute_0_5 : packedMul l0Rows l5Rows = packedMul l5Rows l0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem commute_1_2 : packedMul l1Rows l2Rows = packedMul l2Rows l1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem commute_1_5 : packedMul l1Rows l5Rows = packedMul l5Rows l1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem commute_2_5 : packedMul l2Rows l5Rows = packedMul l5Rows l2Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem commute_0_3 : packedMul l0Rows l3Rows = packedMul l3Rows l0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem commute_0_4 : packedMul l0Rows l4Rows = packedMul l4Rows l0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem commute_3_4 : packedMul l3Rows l4Rows = packedMul l4Rows l3Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem commute_3_5 : packedMul l3Rows l5Rows = packedMul l5Rows l3Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem commute_4_5 : packedMul l4Rows l5Rows = packedMul l5Rows l4Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
end Janko4.LocalStructure.ElementaryEightGeometry.LiftMatrices
