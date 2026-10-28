module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Rows

/-!
# Checked squares and pair commutators of the four outside lifts

These bounded full-matrix checks are transported to the actual native words
in `Relations`. Each certificate is checked by the Lean kernel.
-/

public section
namespace Janko4.LocalStructure.LinearFive.NativeRows
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
set_option maxHeartbeats 800000 in
theorem square_rows_0 : packedMul f0Rows f0Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

set_option maxHeartbeats 800000 in
theorem square_rows_1 : packedMul f1Rows f1Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

set_option maxHeartbeats 800000 in
theorem square_rows_2 : packedMul f2Rows f2Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

set_option maxHeartbeats 800000 in
theorem square_rows_3 : packedMul f3Rows f3Rows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)

set_option maxHeartbeats 800000 in
theorem commute_rows_0_1 :
    packedMul f0Rows f1Rows = packedMul f1Rows f0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)

set_option maxHeartbeats 800000 in
theorem commute_rows_0_2 :
    packedMul f0Rows f2Rows = packedMul f2Rows f0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)

set_option maxHeartbeats 800000 in
theorem commute_rows_0_3 :
    packedMul f0Rows f3Rows = packedMul f3Rows f0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)

set_option maxHeartbeats 800000 in
theorem commute_rows_1_2 :
    packedMul f1Rows f2Rows = packedMul f2Rows f1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)

set_option maxHeartbeats 800000 in
theorem commute_rows_1_3 :
    packedMul f1Rows f3Rows = packedMul f3Rows f1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)

set_option maxHeartbeats 800000 in
theorem commute_rows_2_3 :
    packedMul f2Rows f3Rows = packedMul f3Rows f2Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)

end Janko4.LocalStructure.LinearFive.NativeRows
