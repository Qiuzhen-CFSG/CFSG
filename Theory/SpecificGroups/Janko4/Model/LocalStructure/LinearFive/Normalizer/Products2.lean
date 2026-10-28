module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Products1

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
theorem product_h11 : packedMul h10Rows NativeRows.d17Rows = h11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h12 : packedMul h11Rows NativeRows.d40Rows = h12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h13 : packedMul h12Rows NativeRows.d17Rows = h13Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h14 : packedMul h13Rows NativeRows.d16Rows = h14Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h15 : packedMul h14Rows hshared0Rows = h15Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h16 : packedMul h15Rows NativeRows.d12Rows = h16Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h17 : packedMul h16Rows NativeRows.d19Rows = h17Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h18 : packedMul h17Rows NativeRows.d14Rows = h18Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h19 : packedMul h18Rows NativeRows.d43Rows = h19Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h20 : packedMul h19Rows NativeRows.d9Rows = h20Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_gh : packedMul gRows h20Rows = ghRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_k : packedMul ghRows e0Rows = kRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_ik : packedMul kRows ikRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_n0a : packedMul ikRows uRows = n0aRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_n0 : packedMul n0aRows kRows = n0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_n1a : packedMul ikRows vRows = n1aRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_n1 : packedMul n1aRows kRows = n1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m3 : packedMul (NativeIndependence.generatorRows 0) (NativeIndependence.generatorRows 1) = m3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m7 : packedMul m3Rows (NativeIndependence.generatorRows 2) = m7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m23 : packedMul m7Rows (NativeIndependence.generatorRows 4) = m23Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m55 : packedMul m23Rows (NativeIndependence.generatorRows 5) = m55Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m119 : packedMul m55Rows (NativeIndependence.generatorRows 6) = m119Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m247 : packedMul m119Rows (NativeIndependence.generatorRows 7) = m247Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m36 : packedMul (NativeIndependence.generatorRows 2) (NativeIndependence.generatorRows 5) = m36Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m100 : packedMul m36Rows (NativeIndependence.generatorRows 6) = m100Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.LinearFive.NativeNormalizer
