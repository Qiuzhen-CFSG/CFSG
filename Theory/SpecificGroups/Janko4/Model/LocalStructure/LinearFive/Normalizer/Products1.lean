module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Products0

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
theorem product_iv : packedMul vRows ivRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_r1a : packedMul iuRows rRows = r1aRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_r1 : packedMul r1aRows uRows = r1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_r2a : packedMul ivRows r1Rows = r2aRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_r2 : packedMul r2aRows vRows = r2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_z : packedMul rRows r2Rows = zRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_zt : packedMul zRows (NativeIndependence.generatorRows 0) = ztRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_zt2 : packedMul ztRows ztRows = zt2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_zt4 : packedMul zt2Rows zt2Rows = zt4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_zt8 : packedMul zt4Rows zt4Rows = zt8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_zt16 : packedMul zt8Rows zt8Rows = zt16Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_zt18 : packedMul zt16Rows zt2Rows = zt18Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_g : packedMul zt18Rows ztRows = gRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_hshared0 : packedMul NativeRows.d5Rows yRows = hshared0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h0 : packedMul NativeRows.d20Rows NativeRows.d30Rows = h0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h1 : packedMul h0Rows NativeRows.d21Rows = h1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h2 : packedMul h1Rows NativeRows.d15Rows = h2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h3 : packedMul h2Rows hshared0Rows = h3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h4 : packedMul h3Rows NativeRows.d8Rows = h4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h5 : packedMul h4Rows hshared0Rows = h5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h6 : packedMul h5Rows NativeRows.d41Rows = h6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h7 : packedMul h6Rows NativeRows.d20Rows = h7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h8 : packedMul h7Rows NativeRows.d19Rows = h8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h9 : packedMul h8Rows NativeRows.d27Rows = h9Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_h10 : packedMul h9Rows NativeRows.d15Rows = h10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.LinearFive.NativeNormalizer
