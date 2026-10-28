module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Products2

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
theorem product_m356 : packedMul m100Rows (NativeIndependence.generatorRows 8) = m356Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m868 : packedMul m356Rows (NativeIndependence.generatorRows 9) = m868Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m24 : packedMul (NativeIndependence.generatorRows 3) (NativeIndependence.generatorRows 4) = m24Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m35 : packedMul m3Rows (NativeIndependence.generatorRows 5) = m35Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m291 : packedMul m35Rows (NativeIndependence.generatorRows 8) = m291Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m803 : packedMul m291Rows (NativeIndependence.generatorRows 9) = m803Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m39 : packedMul m7Rows (NativeIndependence.generatorRows 5) = m39Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m295 : packedMul m39Rows (NativeIndependence.generatorRows 8) = m295Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m807 : packedMul m295Rows (NativeIndependence.generatorRows 9) = m807Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m11 : packedMul m3Rows (NativeIndependence.generatorRows 3) = m11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m267 : packedMul m11Rows (NativeIndependence.generatorRows 8) = m267Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m779 : packedMul m267Rows (NativeIndependence.generatorRows 9) = m779Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m129 : packedMul (NativeIndependence.generatorRows 0) (NativeIndependence.generatorRows 7) = m129Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m385 : packedMul m129Rows (NativeIndependence.generatorRows 8) = m385Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m897 : packedMul m385Rows (NativeIndependence.generatorRows 9) = m897Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m6 : packedMul (NativeIndependence.generatorRows 1) (NativeIndependence.generatorRows 2) = m6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m22 : packedMul m6Rows (NativeIndependence.generatorRows 4) = m22Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m54 : packedMul m22Rows (NativeIndependence.generatorRows 5) = m54Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m118 : packedMul m54Rows (NativeIndependence.generatorRows 6) = m118Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m246 : packedMul m118Rows (NativeIndependence.generatorRows 7) = m246Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m502 : packedMul m246Rows (NativeIndependence.generatorRows 8) = m502Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m38 : packedMul m6Rows (NativeIndependence.generatorRows 5) = m38Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m102 : packedMul m38Rows (NativeIndependence.generatorRows 6) = m102Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m358 : packedMul m102Rows (NativeIndependence.generatorRows 8) = m358Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m10 : packedMul (NativeIndependence.generatorRows 1) (NativeIndependence.generatorRows 3) = m10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.LinearFive.NativeNormalizer
