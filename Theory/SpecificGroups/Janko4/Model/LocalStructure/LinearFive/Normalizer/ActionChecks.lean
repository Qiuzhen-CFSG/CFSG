module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Products4

/-!
# Bounded checks for the native normalizer words

Each row-product equality is checked by Lean and decoded to ordinary matrices.
The batches keep kernel arithmetic sequential and reuse all intermediate values.
-/

public section
namespace Janko4.LocalStructure.LinearFive.NativeNormalizer
open GeneratorCertificates Cardinality.KernelCount
set_option maxRecDepth 10000
set_option Elab.async false
set_option maxHeartbeats 800000 in
theorem action_0_0 : packedMul n0Rows (NativeIndependence.generatorRows 0) = packedMul m247Rows n0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_0_1 : packedMul n0Rows (NativeIndependence.generatorRows 1) = packedMul m868Rows n0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_0_2 : packedMul n0Rows (NativeIndependence.generatorRows 2) = packedMul m24Rows n0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_0_3 : packedMul n0Rows (NativeIndependence.generatorRows 3) = packedMul m803Rows n0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_0_4 : packedMul n0Rows (NativeIndependence.generatorRows 4) = packedMul m807Rows n0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_0_5 : packedMul n0Rows (NativeIndependence.generatorRows 5) = packedMul m779Rows n0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_0_6 : packedMul n0Rows (NativeIndependence.generatorRows 6) = packedMul m897Rows n0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_0_7 : packedMul n0Rows (NativeIndependence.generatorRows 7) = packedMul m39Rows n0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_0_8 : packedMul n0Rows (NativeIndependence.generatorRows 8) = packedMul m502Rows n0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_0_9 : packedMul n0Rows (NativeIndependence.generatorRows 9) = packedMul m358Rows n0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_1_0 : packedMul n1Rows (NativeIndependence.generatorRows 0) = packedMul m746Rows n1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_1_1 : packedMul n1Rows (NativeIndependence.generatorRows 1) = packedMul m722Rows n1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_1_2 : packedMul n1Rows (NativeIndependence.generatorRows 2) = packedMul m12Rows n1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_1_3 : packedMul n1Rows (NativeIndependence.generatorRows 3) = packedMul m83Rows n1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_1_4 : packedMul n1Rows (NativeIndependence.generatorRows 4) = packedMul m868Rows n1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_1_5 : packedMul n1Rows (NativeIndependence.generatorRows 5) = packedMul m396Rows n1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_1_6 : packedMul n1Rows (NativeIndependence.generatorRows 6) = packedMul m492Rows n1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_1_7 : packedMul n1Rows (NativeIndependence.generatorRows 7) = packedMul m600Rows n1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_1_8 : packedMul n1Rows (NativeIndependence.generatorRows 8) = packedMul m116Rows n1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem action_1_9 : packedMul n1Rows (NativeIndependence.generatorRows 9) = packedMul m603Rows n1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
end Janko4.LocalStructure.LinearFive.NativeNormalizer
