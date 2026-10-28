module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Products3

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
theorem product_m42 : packedMul m10Rows (NativeIndependence.generatorRows 5) = m42Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m106 : packedMul m42Rows (NativeIndependence.generatorRows 6) = m106Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m234 : packedMul m106Rows (NativeIndependence.generatorRows 7) = m234Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m746 : packedMul m234Rows (NativeIndependence.generatorRows 9) = m746Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m18 : packedMul (NativeIndependence.generatorRows 1) (NativeIndependence.generatorRows 4) = m18Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m82 : packedMul m18Rows (NativeIndependence.generatorRows 6) = m82Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m210 : packedMul m82Rows (NativeIndependence.generatorRows 7) = m210Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m722 : packedMul m210Rows (NativeIndependence.generatorRows 9) = m722Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m12 : packedMul (NativeIndependence.generatorRows 2) (NativeIndependence.generatorRows 3) = m12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m19 : packedMul m3Rows (NativeIndependence.generatorRows 4) = m19Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m83 : packedMul m19Rows (NativeIndependence.generatorRows 6) = m83Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m140 : packedMul m12Rows (NativeIndependence.generatorRows 7) = m140Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m396 : packedMul m140Rows (NativeIndependence.generatorRows 8) = m396Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m44 : packedMul m12Rows (NativeIndependence.generatorRows 5) = m44Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m108 : packedMul m44Rows (NativeIndependence.generatorRows 6) = m108Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m236 : packedMul m108Rows (NativeIndependence.generatorRows 7) = m236Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m492 : packedMul m236Rows (NativeIndependence.generatorRows 8) = m492Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m88 : packedMul m24Rows (NativeIndependence.generatorRows 6) = m88Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m600 : packedMul m88Rows (NativeIndependence.generatorRows 9) = m600Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m20 : packedMul (NativeIndependence.generatorRows 2) (NativeIndependence.generatorRows 4) = m20Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m52 : packedMul m20Rows (NativeIndependence.generatorRows 5) = m52Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m116 : packedMul m52Rows (NativeIndependence.generatorRows 6) = m116Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m27 : packedMul m11Rows (NativeIndependence.generatorRows 4) = m27Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m91 : packedMul m27Rows (NativeIndependence.generatorRows 6) = m91Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_m603 : packedMul m91Rows (NativeIndependence.generatorRows 9) = m603Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.LinearFive.NativeNormalizer
