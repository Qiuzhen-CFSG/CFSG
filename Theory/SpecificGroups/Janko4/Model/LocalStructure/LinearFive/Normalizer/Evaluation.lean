module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.ActionChecks
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Words
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Mask

/-!
# Evaluation of the actual native normalizer words

The faithful native representation transports the factored product certificates
back to J₄. In particular the twenty identities below use left conjugation and
the original ten generators of F; no abstract matrix group is substituted for F.
-/

public noncomputable section
namespace Janko4.LocalStructure.LinearFive.NativeNormalizer
open Cardinality KernelCount KernelCount.Relations GeneratorCertificates
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis
private theorem eval_a : toMatrix (sourceA matrixA_mul_self) = decodeRows aRows := by
  simpa only [matrixA] using toMatrix_sourceA matrixA_mul_self
private theorem eval_b : toMatrix (sourceB matrixB_pow_four) = decodeRows bRows := by
  simpa only [matrixB] using toMatrix_sourceB matrixB_pow_four
private theorem eval_x : toMatrix (localX matrixA_mul_self matrixB_pow_four : Model) = decodeRows xRows :=
  representation_x _ _
private theorem eval_ix : toMatrix (localX matrixA_mul_self matrixB_pow_four : Model)⁻¹ = decodeRows xRows := by
  have hi : (localX matrixA_mul_self matrixB_pow_four : Model)⁻¹ =
      (localX matrixA_mul_self matrixB_pow_four : Model) := by
    apply inv_eq_of_mul_eq_one_left
    exact congrArg (fun a : M => (a : Model)) (localX_mul_self matrixA_mul_self matrixB_pow_four)
  rw [hi]
  exact eval_x
private theorem eval_y : toMatrix (localY matrixA_mul_self matrixB_pow_four : Model) = decodeRows yRows :=
  representation_y _ _
private theorem eval_iy : toMatrix (localY matrixA_mul_self matrixB_pow_four : Model)⁻¹ = decodeRows NativeRows.iyRows :=
  eval_inv toMatrix eval_y (by rw [decoded_product NativeRows.inverse_y, decode_packedOne])
private theorem eval_e0 : toMatrix (kernelValue 1 : Model) = decodeRows e0Rows := by
  rw [show kernelValue 1 = localKernelSeed matrixA_mul_self matrixB_pow_four from
    Simplicity.Max1Fusion.KernelOrbits.maskValue_one _ _]
  exact representation_seed _ _
private theorem eval_generator (i : Fin 10) : toMatrix (generators i : Model) =
    decodeRows (NativeIndependence.generatorRows i) := representation_generators i
private theorem eval_d3 : toMatrix (NativeWords.d3 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d3Rows :=
  eval_mul toMatrix eval_x eval_y (decoded_product NativeRows.product_d3)
private theorem eval_d4 : toMatrix (NativeWords.d4 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d4Rows :=
  eval_mul toMatrix eval_x eval_iy (decoded_product NativeRows.product_d4)
private theorem eval_d5 : toMatrix (NativeWords.d5 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d5Rows :=
  eval_mul toMatrix eval_ix eval_y (decoded_product NativeRows.product_d5)
private theorem eval_d6 : toMatrix (NativeWords.d6 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d6Rows :=
  eval_mul toMatrix eval_ix eval_iy (decoded_product NativeRows.product_d6)
private theorem eval_d7 : toMatrix (NativeWords.d7 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d7Rows :=
  eval_mul toMatrix eval_d4 eval_d3 (decoded_product NativeRows.product_d7)
private theorem eval_d8 : toMatrix (NativeWords.d8 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d8Rows :=
  eval_mul toMatrix eval_d5 eval_d5 (decoded_product NativeRows.product_d8)
private theorem eval_d9 : toMatrix (NativeWords.d9 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d9Rows :=
  eval_mul toMatrix eval_d6 eval_d6 (decoded_product NativeRows.product_d9)
private theorem eval_d10 : toMatrix (NativeWords.d10 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d10Rows :=
  eval_mul toMatrix eval_d4 eval_d7 (decoded_product NativeRows.product_d10)
private theorem eval_d11 : toMatrix (NativeWords.d11 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d11Rows :=
  eval_mul toMatrix eval_d3 eval_d3 (decoded_product NativeRows.product_d11)
private theorem eval_d12 : toMatrix (NativeWords.d12 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d12Rows :=
  eval_mul toMatrix eval_d4 eval_d10 (decoded_product NativeRows.product_d12)
private theorem eval_d13 : toMatrix (NativeWords.d13 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d13Rows :=
  eval_mul toMatrix eval_d5 eval_d6 (decoded_product NativeRows.product_d13)
private theorem eval_d14 : toMatrix (NativeWords.d14 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d14Rows :=
  eval_mul toMatrix eval_d3 eval_d7 (decoded_product NativeRows.product_d14)
private theorem eval_d15 : toMatrix (NativeWords.d15 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d15Rows :=
  eval_mul toMatrix eval_d5 eval_d9 (decoded_product NativeRows.product_d15)
private theorem eval_d16 : toMatrix (NativeWords.d16 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d16Rows :=
  eval_mul toMatrix eval_d7 eval_d11 (decoded_product NativeRows.product_d16)
private theorem eval_d17 : toMatrix (NativeWords.d17 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d17Rows :=
  eval_mul toMatrix eval_d13 eval_d8 (decoded_product NativeRows.product_d17)
private theorem eval_d19 : toMatrix (NativeWords.d19 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d19Rows :=
  eval_mul toMatrix eval_d4 eval_d12 (decoded_product NativeRows.product_d19)
private theorem eval_d20 : toMatrix (NativeWords.d20 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d20Rows :=
  eval_mul toMatrix eval_d6 eval_d8 (decoded_product NativeRows.product_d20)
private theorem eval_d21 : toMatrix (NativeWords.d21 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d21Rows :=
  eval_mul toMatrix eval_d3 eval_d12 (decoded_product NativeRows.product_d21)
private theorem eval_d22 : toMatrix (NativeWords.d22 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d22Rows :=
  eval_mul toMatrix eval_d7 eval_d14 (decoded_product NativeRows.product_d22)
private theorem eval_d27 : toMatrix (NativeWords.d27 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d27Rows :=
  eval_mul toMatrix eval_d11 eval_d16 (decoded_product NativeRows.product_d27)
private theorem eval_d30 : toMatrix (NativeWords.d30 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d30Rows :=
  eval_mul toMatrix eval_d4 eval_x (decoded_product NativeRows.product_d30)
private theorem eval_d40 : toMatrix (NativeWords.d40 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d40Rows :=
  eval_mul toMatrix eval_d3 eval_x (decoded_product NativeRows.product_d40)
private theorem eval_d41 : toMatrix (NativeWords.d41 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d41Rows :=
  eval_mul toMatrix eval_d22 eval_d11 (decoded_product NativeRows.product_d41)
private theorem eval_d43 : toMatrix (NativeWords.d43 (localX matrixA_mul_self matrixB_pow_four : Model) (localY matrixA_mul_self matrixB_pow_four : Model)) = decodeRows NativeRows.d43Rows :=
  eval_mul toMatrix eval_d9 eval_d6 (decoded_product NativeRows.product_d43)
private theorem eval_ab : toMatrix ab = decodeRows abRows :=
  eval_mul toMatrix eval_a eval_b (decoded_product product_ab)
private theorem eval_b2 : toMatrix b2 = decodeRows b2Rows :=
  eval_mul toMatrix eval_b eval_b (decoded_product product_b2)
private theorem eval_b3 : toMatrix b3 = decodeRows b3Rows :=
  eval_mul toMatrix eval_b2 eval_b (decoded_product product_b3)
private theorem eval_ab3 : toMatrix ab3 = decodeRows ab3Rows :=
  eval_mul toMatrix eval_a eval_b3 (decoded_product product_ab3)
private theorem eval_t2 : toMatrix t2 = decodeRows t2Rows :=
  eval_mul toMatrix eval_ab3 eval_ab3 (decoded_product product_t2)
private theorem eval_t4 : toMatrix t4 = decodeRows t4Rows :=
  eval_mul toMatrix eval_t2 eval_t2 (decoded_product product_t4)
private theorem eval_it4 : toMatrix it4 = decodeRows it4Rows :=
  eval_inv toMatrix eval_t4 (by rw [decoded_product product_it4, decode_packedOne])
private theorem eval_ua : toMatrix ua = decodeRows uaRows :=
  eval_mul toMatrix eval_it4 eval_a (decoded_product product_ua)
theorem eval_u : toMatrix u = decodeRows uRows :=
  eval_mul toMatrix eval_ua eval_t4 (decoded_product product_u)
private theorem eval_s2 : toMatrix s2 = decodeRows s2Rows :=
  eval_mul toMatrix eval_ab eval_ab (decoded_product product_s2)
private theorem eval_s4 : toMatrix s4 = decodeRows s4Rows :=
  eval_mul toMatrix eval_s2 eval_s2 (decoded_product product_s4)
private theorem eval_s8 : toMatrix s8 = decodeRows s8Rows :=
  eval_mul toMatrix eval_s4 eval_s4 (decoded_product product_s8)
private theorem eval_is8 : toMatrix is8 = decodeRows is8Rows :=
  eval_inv toMatrix eval_s8 (by rw [decoded_product product_is8, decode_packedOne])
private theorem eval_vb : toMatrix vb = decodeRows vbRows :=
  eval_mul toMatrix eval_is8 eval_b (decoded_product product_vb)
theorem eval_v : toMatrix v = decodeRows vRows :=
  eval_mul toMatrix eval_vb eval_s8 (decoded_product product_v)
private theorem eval_v2 : toMatrix v2 = decodeRows v2Rows :=
  eval_mul toMatrix eval_v eval_v (decoded_product product_v2)
private theorem eval_v3 : toMatrix v3 = decodeRows v3Rows :=
  eval_mul toMatrix eval_v2 eval_v (decoded_product product_v3)
private theorem eval_w0 : toMatrix w0 = decodeRows w0Rows :=
  eval_mul toMatrix eval_v2 eval_u (decoded_product product_w0)
private theorem eval_w1 : toMatrix w1 = decodeRows w1Rows :=
  eval_mul toMatrix eval_w0 eval_v3 (decoded_product product_w1)
private theorem eval_w2 : toMatrix w2 = decodeRows w2Rows :=
  eval_mul toMatrix eval_w1 eval_u (decoded_product product_w2)
private theorem eval_w3 : toMatrix w3 = decodeRows w3Rows :=
  eval_mul toMatrix eval_w2 eval_v (decoded_product product_w3)
private theorem eval_w : toMatrix w = decodeRows wRows :=
  eval_mul toMatrix eval_w3 eval_u (decoded_product product_w)
private theorem eval_w4a : toMatrix w4a = decodeRows w4aRows :=
  eval_mul toMatrix eval_w eval_w (decoded_product product_w4a)
private theorem eval_r : toMatrix r = decodeRows rRows :=
  eval_mul toMatrix eval_w4a eval_w4a (decoded_product product_r)
private theorem eval_iu : toMatrix iu = decodeRows iuRows :=
  eval_inv toMatrix eval_u (by rw [decoded_product product_iu, decode_packedOne])
private theorem eval_iv : toMatrix iv = decodeRows ivRows :=
  eval_inv toMatrix eval_v (by rw [decoded_product product_iv, decode_packedOne])
private theorem eval_r1a : toMatrix r1a = decodeRows r1aRows :=
  eval_mul toMatrix eval_iu eval_r (decoded_product product_r1a)
private theorem eval_r1 : toMatrix r1 = decodeRows r1Rows :=
  eval_mul toMatrix eval_r1a eval_u (decoded_product product_r1)
private theorem eval_r2a : toMatrix r2a = decodeRows r2aRows :=
  eval_mul toMatrix eval_iv eval_r1 (decoded_product product_r2a)
private theorem eval_r2 : toMatrix r2 = decodeRows r2Rows :=
  eval_mul toMatrix eval_r2a eval_v (decoded_product product_r2)
private theorem eval_z : toMatrix z = decodeRows zRows :=
  eval_mul toMatrix eval_r eval_r2 (decoded_product product_z)
private theorem eval_zt : toMatrix zt = decodeRows ztRows :=
  eval_mul toMatrix eval_z (eval_generator 0) (decoded_product product_zt)
private theorem eval_zt2 : toMatrix zt2 = decodeRows zt2Rows :=
  eval_mul toMatrix eval_zt eval_zt (decoded_product product_zt2)
private theorem eval_zt4 : toMatrix zt4 = decodeRows zt4Rows :=
  eval_mul toMatrix eval_zt2 eval_zt2 (decoded_product product_zt4)
private theorem eval_zt8 : toMatrix zt8 = decodeRows zt8Rows :=
  eval_mul toMatrix eval_zt4 eval_zt4 (decoded_product product_zt8)
private theorem eval_zt16 : toMatrix zt16 = decodeRows zt16Rows :=
  eval_mul toMatrix eval_zt8 eval_zt8 (decoded_product product_zt16)
private theorem eval_zt18 : toMatrix zt18 = decodeRows zt18Rows :=
  eval_mul toMatrix eval_zt16 eval_zt2 (decoded_product product_zt18)
private theorem eval_g : toMatrix g = decodeRows gRows :=
  eval_mul toMatrix eval_zt18 eval_zt (decoded_product product_g)
private theorem eval_hshared0 : toMatrix hshared0 = decodeRows hshared0Rows :=
  eval_mul toMatrix eval_d5 eval_y (decoded_product product_hshared0)
private theorem eval_h0 : toMatrix h0 = decodeRows h0Rows :=
  eval_mul toMatrix eval_d20 eval_d30 (decoded_product product_h0)
private theorem eval_h1 : toMatrix h1 = decodeRows h1Rows :=
  eval_mul toMatrix eval_h0 eval_d21 (decoded_product product_h1)
private theorem eval_h2 : toMatrix h2 = decodeRows h2Rows :=
  eval_mul toMatrix eval_h1 eval_d15 (decoded_product product_h2)
private theorem eval_h3 : toMatrix h3 = decodeRows h3Rows :=
  eval_mul toMatrix eval_h2 eval_hshared0 (decoded_product product_h3)
private theorem eval_h4 : toMatrix h4 = decodeRows h4Rows :=
  eval_mul toMatrix eval_h3 eval_d8 (decoded_product product_h4)
private theorem eval_h5 : toMatrix h5 = decodeRows h5Rows :=
  eval_mul toMatrix eval_h4 eval_hshared0 (decoded_product product_h5)
private theorem eval_h6 : toMatrix h6 = decodeRows h6Rows :=
  eval_mul toMatrix eval_h5 eval_d41 (decoded_product product_h6)
private theorem eval_h7 : toMatrix h7 = decodeRows h7Rows :=
  eval_mul toMatrix eval_h6 eval_d20 (decoded_product product_h7)
private theorem eval_h8 : toMatrix h8 = decodeRows h8Rows :=
  eval_mul toMatrix eval_h7 eval_d19 (decoded_product product_h8)
private theorem eval_h9 : toMatrix h9 = decodeRows h9Rows :=
  eval_mul toMatrix eval_h8 eval_d27 (decoded_product product_h9)
private theorem eval_h10 : toMatrix h10 = decodeRows h10Rows :=
  eval_mul toMatrix eval_h9 eval_d15 (decoded_product product_h10)
private theorem eval_h11 : toMatrix h11 = decodeRows h11Rows :=
  eval_mul toMatrix eval_h10 eval_d17 (decoded_product product_h11)
private theorem eval_h12 : toMatrix h12 = decodeRows h12Rows :=
  eval_mul toMatrix eval_h11 eval_d40 (decoded_product product_h12)
private theorem eval_h13 : toMatrix h13 = decodeRows h13Rows :=
  eval_mul toMatrix eval_h12 eval_d17 (decoded_product product_h13)
private theorem eval_h14 : toMatrix h14 = decodeRows h14Rows :=
  eval_mul toMatrix eval_h13 eval_d16 (decoded_product product_h14)
private theorem eval_h15 : toMatrix h15 = decodeRows h15Rows :=
  eval_mul toMatrix eval_h14 eval_hshared0 (decoded_product product_h15)
private theorem eval_h16 : toMatrix h16 = decodeRows h16Rows :=
  eval_mul toMatrix eval_h15 eval_d12 (decoded_product product_h16)
private theorem eval_h17 : toMatrix h17 = decodeRows h17Rows :=
  eval_mul toMatrix eval_h16 eval_d19 (decoded_product product_h17)
private theorem eval_h18 : toMatrix h18 = decodeRows h18Rows :=
  eval_mul toMatrix eval_h17 eval_d14 (decoded_product product_h18)
private theorem eval_h19 : toMatrix h19 = decodeRows h19Rows :=
  eval_mul toMatrix eval_h18 eval_d43 (decoded_product product_h19)
private theorem eval_h20 : toMatrix h20 = decodeRows h20Rows :=
  eval_mul toMatrix eval_h19 eval_d9 (decoded_product product_h20)
private theorem eval_gh : toMatrix gh = decodeRows ghRows :=
  eval_mul toMatrix eval_g eval_h20 (decoded_product product_gh)
theorem eval_k : toMatrix k = decodeRows kRows :=
  eval_mul toMatrix eval_gh eval_e0 (decoded_product product_k)
private theorem eval_ik : toMatrix ik = decodeRows ikRows :=
  eval_inv toMatrix eval_k (by rw [decoded_product product_ik, decode_packedOne])
private theorem eval_n0a : toMatrix n0a = decodeRows n0aRows :=
  eval_mul toMatrix eval_ik eval_u (decoded_product product_n0a)
theorem eval_n0 : toMatrix n0 = decodeRows n0Rows :=
  eval_mul toMatrix eval_n0a eval_k (decoded_product product_n0)
private theorem eval_n1a : toMatrix n1a = decodeRows n1aRows :=
  eval_mul toMatrix eval_ik eval_v (decoded_product product_n1a)
theorem eval_n1 : toMatrix n1 = decodeRows n1Rows :=
  eval_mul toMatrix eval_n1a eval_k (decoded_product product_n1)
private theorem eval_m3 : toMatrix m3 = decodeRows m3Rows :=
  eval_mul toMatrix (eval_generator 0) (eval_generator 1) (decoded_product product_m3)
private theorem eval_m7 : toMatrix m7 = decodeRows m7Rows :=
  eval_mul toMatrix eval_m3 (eval_generator 2) (decoded_product product_m7)
private theorem eval_m23 : toMatrix m23 = decodeRows m23Rows :=
  eval_mul toMatrix eval_m7 (eval_generator 4) (decoded_product product_m23)
private theorem eval_m55 : toMatrix m55 = decodeRows m55Rows :=
  eval_mul toMatrix eval_m23 (eval_generator 5) (decoded_product product_m55)
private theorem eval_m119 : toMatrix m119 = decodeRows m119Rows :=
  eval_mul toMatrix eval_m55 (eval_generator 6) (decoded_product product_m119)
private theorem eval_m247 : toMatrix m247 = decodeRows m247Rows :=
  eval_mul toMatrix eval_m119 (eval_generator 7) (decoded_product product_m247)
private theorem eval_m36 : toMatrix m36 = decodeRows m36Rows :=
  eval_mul toMatrix (eval_generator 2) (eval_generator 5) (decoded_product product_m36)
private theorem eval_m100 : toMatrix m100 = decodeRows m100Rows :=
  eval_mul toMatrix eval_m36 (eval_generator 6) (decoded_product product_m100)
private theorem eval_m356 : toMatrix m356 = decodeRows m356Rows :=
  eval_mul toMatrix eval_m100 (eval_generator 8) (decoded_product product_m356)
private theorem eval_m868 : toMatrix m868 = decodeRows m868Rows :=
  eval_mul toMatrix eval_m356 (eval_generator 9) (decoded_product product_m868)
private theorem eval_m24 : toMatrix m24 = decodeRows m24Rows :=
  eval_mul toMatrix (eval_generator 3) (eval_generator 4) (decoded_product product_m24)
private theorem eval_m35 : toMatrix m35 = decodeRows m35Rows :=
  eval_mul toMatrix eval_m3 (eval_generator 5) (decoded_product product_m35)
private theorem eval_m291 : toMatrix m291 = decodeRows m291Rows :=
  eval_mul toMatrix eval_m35 (eval_generator 8) (decoded_product product_m291)
private theorem eval_m803 : toMatrix m803 = decodeRows m803Rows :=
  eval_mul toMatrix eval_m291 (eval_generator 9) (decoded_product product_m803)
private theorem eval_m39 : toMatrix m39 = decodeRows m39Rows :=
  eval_mul toMatrix eval_m7 (eval_generator 5) (decoded_product product_m39)
private theorem eval_m295 : toMatrix m295 = decodeRows m295Rows :=
  eval_mul toMatrix eval_m39 (eval_generator 8) (decoded_product product_m295)
private theorem eval_m807 : toMatrix m807 = decodeRows m807Rows :=
  eval_mul toMatrix eval_m295 (eval_generator 9) (decoded_product product_m807)
private theorem eval_m11 : toMatrix m11 = decodeRows m11Rows :=
  eval_mul toMatrix eval_m3 (eval_generator 3) (decoded_product product_m11)
private theorem eval_m267 : toMatrix m267 = decodeRows m267Rows :=
  eval_mul toMatrix eval_m11 (eval_generator 8) (decoded_product product_m267)
private theorem eval_m779 : toMatrix m779 = decodeRows m779Rows :=
  eval_mul toMatrix eval_m267 (eval_generator 9) (decoded_product product_m779)
private theorem eval_m129 : toMatrix m129 = decodeRows m129Rows :=
  eval_mul toMatrix (eval_generator 0) (eval_generator 7) (decoded_product product_m129)
private theorem eval_m385 : toMatrix m385 = decodeRows m385Rows :=
  eval_mul toMatrix eval_m129 (eval_generator 8) (decoded_product product_m385)
private theorem eval_m897 : toMatrix m897 = decodeRows m897Rows :=
  eval_mul toMatrix eval_m385 (eval_generator 9) (decoded_product product_m897)
private theorem eval_m6 : toMatrix m6 = decodeRows m6Rows :=
  eval_mul toMatrix (eval_generator 1) (eval_generator 2) (decoded_product product_m6)
private theorem eval_m22 : toMatrix m22 = decodeRows m22Rows :=
  eval_mul toMatrix eval_m6 (eval_generator 4) (decoded_product product_m22)
private theorem eval_m54 : toMatrix m54 = decodeRows m54Rows :=
  eval_mul toMatrix eval_m22 (eval_generator 5) (decoded_product product_m54)
private theorem eval_m118 : toMatrix m118 = decodeRows m118Rows :=
  eval_mul toMatrix eval_m54 (eval_generator 6) (decoded_product product_m118)
private theorem eval_m246 : toMatrix m246 = decodeRows m246Rows :=
  eval_mul toMatrix eval_m118 (eval_generator 7) (decoded_product product_m246)
private theorem eval_m502 : toMatrix m502 = decodeRows m502Rows :=
  eval_mul toMatrix eval_m246 (eval_generator 8) (decoded_product product_m502)
private theorem eval_m38 : toMatrix m38 = decodeRows m38Rows :=
  eval_mul toMatrix eval_m6 (eval_generator 5) (decoded_product product_m38)
private theorem eval_m102 : toMatrix m102 = decodeRows m102Rows :=
  eval_mul toMatrix eval_m38 (eval_generator 6) (decoded_product product_m102)
private theorem eval_m358 : toMatrix m358 = decodeRows m358Rows :=
  eval_mul toMatrix eval_m102 (eval_generator 8) (decoded_product product_m358)
private theorem eval_m10 : toMatrix m10 = decodeRows m10Rows :=
  eval_mul toMatrix (eval_generator 1) (eval_generator 3) (decoded_product product_m10)
private theorem eval_m42 : toMatrix m42 = decodeRows m42Rows :=
  eval_mul toMatrix eval_m10 (eval_generator 5) (decoded_product product_m42)
private theorem eval_m106 : toMatrix m106 = decodeRows m106Rows :=
  eval_mul toMatrix eval_m42 (eval_generator 6) (decoded_product product_m106)
private theorem eval_m234 : toMatrix m234 = decodeRows m234Rows :=
  eval_mul toMatrix eval_m106 (eval_generator 7) (decoded_product product_m234)
private theorem eval_m746 : toMatrix m746 = decodeRows m746Rows :=
  eval_mul toMatrix eval_m234 (eval_generator 9) (decoded_product product_m746)
private theorem eval_m18 : toMatrix m18 = decodeRows m18Rows :=
  eval_mul toMatrix (eval_generator 1) (eval_generator 4) (decoded_product product_m18)
private theorem eval_m82 : toMatrix m82 = decodeRows m82Rows :=
  eval_mul toMatrix eval_m18 (eval_generator 6) (decoded_product product_m82)
private theorem eval_m210 : toMatrix m210 = decodeRows m210Rows :=
  eval_mul toMatrix eval_m82 (eval_generator 7) (decoded_product product_m210)
private theorem eval_m722 : toMatrix m722 = decodeRows m722Rows :=
  eval_mul toMatrix eval_m210 (eval_generator 9) (decoded_product product_m722)
private theorem eval_m12 : toMatrix m12 = decodeRows m12Rows :=
  eval_mul toMatrix (eval_generator 2) (eval_generator 3) (decoded_product product_m12)
private theorem eval_m19 : toMatrix m19 = decodeRows m19Rows :=
  eval_mul toMatrix eval_m3 (eval_generator 4) (decoded_product product_m19)
private theorem eval_m83 : toMatrix m83 = decodeRows m83Rows :=
  eval_mul toMatrix eval_m19 (eval_generator 6) (decoded_product product_m83)
private theorem eval_m140 : toMatrix m140 = decodeRows m140Rows :=
  eval_mul toMatrix eval_m12 (eval_generator 7) (decoded_product product_m140)
private theorem eval_m396 : toMatrix m396 = decodeRows m396Rows :=
  eval_mul toMatrix eval_m140 (eval_generator 8) (decoded_product product_m396)
private theorem eval_m44 : toMatrix m44 = decodeRows m44Rows :=
  eval_mul toMatrix eval_m12 (eval_generator 5) (decoded_product product_m44)
private theorem eval_m108 : toMatrix m108 = decodeRows m108Rows :=
  eval_mul toMatrix eval_m44 (eval_generator 6) (decoded_product product_m108)
private theorem eval_m236 : toMatrix m236 = decodeRows m236Rows :=
  eval_mul toMatrix eval_m108 (eval_generator 7) (decoded_product product_m236)
private theorem eval_m492 : toMatrix m492 = decodeRows m492Rows :=
  eval_mul toMatrix eval_m236 (eval_generator 8) (decoded_product product_m492)
private theorem eval_m88 : toMatrix m88 = decodeRows m88Rows :=
  eval_mul toMatrix eval_m24 (eval_generator 6) (decoded_product product_m88)
private theorem eval_m600 : toMatrix m600 = decodeRows m600Rows :=
  eval_mul toMatrix eval_m88 (eval_generator 9) (decoded_product product_m600)
private theorem eval_m20 : toMatrix m20 = decodeRows m20Rows :=
  eval_mul toMatrix (eval_generator 2) (eval_generator 4) (decoded_product product_m20)
private theorem eval_m52 : toMatrix m52 = decodeRows m52Rows :=
  eval_mul toMatrix eval_m20 (eval_generator 5) (decoded_product product_m52)
private theorem eval_m116 : toMatrix m116 = decodeRows m116Rows :=
  eval_mul toMatrix eval_m52 (eval_generator 6) (decoded_product product_m116)
private theorem eval_m27 : toMatrix m27 = decodeRows m27Rows :=
  eval_mul toMatrix eval_m11 (eval_generator 4) (decoded_product product_m27)
private theorem eval_m91 : toMatrix m91 = decodeRows m91Rows :=
  eval_mul toMatrix eval_m27 (eval_generator 6) (decoded_product product_m91)
private theorem eval_m603 : toMatrix m603 = decodeRows m603Rows :=
  eval_mul toMatrix eval_m91 (eval_generator 9) (decoded_product product_m603)
private theorem mask_basis_0 : fValue 1 = (generators 0 : Model) :=
  fValue_basis 0
private theorem mask_basis_1 : fValue 2 = (generators 1 : Model) :=
  fValue_basis 1
private theorem mask_basis_2 : fValue 4 = (generators 2 : Model) :=
  fValue_basis 2
private theorem mask_basis_3 : fValue 8 = (generators 3 : Model) :=
  fValue_basis 3
private theorem mask_basis_4 : fValue 16 = (generators 4 : Model) :=
  fValue_basis 4
private theorem mask_basis_5 : fValue 32 = (generators 5 : Model) :=
  fValue_basis 5
private theorem mask_basis_6 : fValue 64 = (generators 6 : Model) :=
  fValue_basis 6
private theorem mask_basis_7 : fValue 128 = (generators 7 : Model) :=
  fValue_basis 7
private theorem mask_basis_8 : fValue 256 = (generators 8 : Model) :=
  fValue_basis 8
private theorem mask_basis_9 : fValue 512 = (generators 9 : Model) :=
  fValue_basis 9
private theorem mask_3 : fValue 3 = m3 := by
  rw [show 3 = Nat.xor 1 2 from rfl, fValue_xor, mask_basis_0, mask_basis_1]
  rfl
private theorem mask_7 : fValue 7 = m7 := by
  rw [show 7 = Nat.xor 3 4 from rfl, fValue_xor, mask_3, mask_basis_2]
  rfl
private theorem mask_23 : fValue 23 = m23 := by
  rw [show 23 = Nat.xor 7 16 from rfl, fValue_xor, mask_7, mask_basis_4]
  rfl
private theorem mask_55 : fValue 55 = m55 := by
  rw [show 55 = Nat.xor 23 32 from rfl, fValue_xor, mask_23, mask_basis_5]
  rfl
private theorem mask_119 : fValue 119 = m119 := by
  rw [show 119 = Nat.xor 55 64 from rfl, fValue_xor, mask_55, mask_basis_6]
  rfl
private theorem mask_247 : fValue 247 = m247 := by
  rw [show 247 = Nat.xor 119 128 from rfl, fValue_xor, mask_119, mask_basis_7]
  rfl
private theorem mask_36 : fValue 36 = m36 := by
  rw [show 36 = Nat.xor 4 32 from rfl, fValue_xor, mask_basis_2, mask_basis_5]
  rfl
private theorem mask_100 : fValue 100 = m100 := by
  rw [show 100 = Nat.xor 36 64 from rfl, fValue_xor, mask_36, mask_basis_6]
  rfl
private theorem mask_356 : fValue 356 = m356 := by
  rw [show 356 = Nat.xor 100 256 from rfl, fValue_xor, mask_100, mask_basis_8]
  rfl
private theorem mask_868 : fValue 868 = m868 := by
  rw [show 868 = Nat.xor 356 512 from rfl, fValue_xor, mask_356, mask_basis_9]
  rfl
private theorem mask_24 : fValue 24 = m24 := by
  rw [show 24 = Nat.xor 8 16 from rfl, fValue_xor, mask_basis_3, mask_basis_4]
  rfl
private theorem mask_35 : fValue 35 = m35 := by
  rw [show 35 = Nat.xor 3 32 from rfl, fValue_xor, mask_3, mask_basis_5]
  rfl
private theorem mask_291 : fValue 291 = m291 := by
  rw [show 291 = Nat.xor 35 256 from rfl, fValue_xor, mask_35, mask_basis_8]
  rfl
private theorem mask_803 : fValue 803 = m803 := by
  rw [show 803 = Nat.xor 291 512 from rfl, fValue_xor, mask_291, mask_basis_9]
  rfl
private theorem mask_39 : fValue 39 = m39 := by
  rw [show 39 = Nat.xor 7 32 from rfl, fValue_xor, mask_7, mask_basis_5]
  rfl
private theorem mask_295 : fValue 295 = m295 := by
  rw [show 295 = Nat.xor 39 256 from rfl, fValue_xor, mask_39, mask_basis_8]
  rfl
private theorem mask_807 : fValue 807 = m807 := by
  rw [show 807 = Nat.xor 295 512 from rfl, fValue_xor, mask_295, mask_basis_9]
  rfl
private theorem mask_11 : fValue 11 = m11 := by
  rw [show 11 = Nat.xor 3 8 from rfl, fValue_xor, mask_3, mask_basis_3]
  rfl
private theorem mask_267 : fValue 267 = m267 := by
  rw [show 267 = Nat.xor 11 256 from rfl, fValue_xor, mask_11, mask_basis_8]
  rfl
private theorem mask_779 : fValue 779 = m779 := by
  rw [show 779 = Nat.xor 267 512 from rfl, fValue_xor, mask_267, mask_basis_9]
  rfl
private theorem mask_129 : fValue 129 = m129 := by
  rw [show 129 = Nat.xor 1 128 from rfl, fValue_xor, mask_basis_0, mask_basis_7]
  rfl
private theorem mask_385 : fValue 385 = m385 := by
  rw [show 385 = Nat.xor 129 256 from rfl, fValue_xor, mask_129, mask_basis_8]
  rfl
private theorem mask_897 : fValue 897 = m897 := by
  rw [show 897 = Nat.xor 385 512 from rfl, fValue_xor, mask_385, mask_basis_9]
  rfl
private theorem mask_6 : fValue 6 = m6 := by
  rw [show 6 = Nat.xor 2 4 from rfl, fValue_xor, mask_basis_1, mask_basis_2]
  rfl
private theorem mask_22 : fValue 22 = m22 := by
  rw [show 22 = Nat.xor 6 16 from rfl, fValue_xor, mask_6, mask_basis_4]
  rfl
private theorem mask_54 : fValue 54 = m54 := by
  rw [show 54 = Nat.xor 22 32 from rfl, fValue_xor, mask_22, mask_basis_5]
  rfl
private theorem mask_118 : fValue 118 = m118 := by
  rw [show 118 = Nat.xor 54 64 from rfl, fValue_xor, mask_54, mask_basis_6]
  rfl
private theorem mask_246 : fValue 246 = m246 := by
  rw [show 246 = Nat.xor 118 128 from rfl, fValue_xor, mask_118, mask_basis_7]
  rfl
private theorem mask_502 : fValue 502 = m502 := by
  rw [show 502 = Nat.xor 246 256 from rfl, fValue_xor, mask_246, mask_basis_8]
  rfl
private theorem mask_38 : fValue 38 = m38 := by
  rw [show 38 = Nat.xor 6 32 from rfl, fValue_xor, mask_6, mask_basis_5]
  rfl
private theorem mask_102 : fValue 102 = m102 := by
  rw [show 102 = Nat.xor 38 64 from rfl, fValue_xor, mask_38, mask_basis_6]
  rfl
private theorem mask_358 : fValue 358 = m358 := by
  rw [show 358 = Nat.xor 102 256 from rfl, fValue_xor, mask_102, mask_basis_8]
  rfl
private theorem mask_10 : fValue 10 = m10 := by
  rw [show 10 = Nat.xor 2 8 from rfl, fValue_xor, mask_basis_1, mask_basis_3]
  rfl
private theorem mask_42 : fValue 42 = m42 := by
  rw [show 42 = Nat.xor 10 32 from rfl, fValue_xor, mask_10, mask_basis_5]
  rfl
private theorem mask_106 : fValue 106 = m106 := by
  rw [show 106 = Nat.xor 42 64 from rfl, fValue_xor, mask_42, mask_basis_6]
  rfl
private theorem mask_234 : fValue 234 = m234 := by
  rw [show 234 = Nat.xor 106 128 from rfl, fValue_xor, mask_106, mask_basis_7]
  rfl
private theorem mask_746 : fValue 746 = m746 := by
  rw [show 746 = Nat.xor 234 512 from rfl, fValue_xor, mask_234, mask_basis_9]
  rfl
private theorem mask_18 : fValue 18 = m18 := by
  rw [show 18 = Nat.xor 2 16 from rfl, fValue_xor, mask_basis_1, mask_basis_4]
  rfl
private theorem mask_82 : fValue 82 = m82 := by
  rw [show 82 = Nat.xor 18 64 from rfl, fValue_xor, mask_18, mask_basis_6]
  rfl
private theorem mask_210 : fValue 210 = m210 := by
  rw [show 210 = Nat.xor 82 128 from rfl, fValue_xor, mask_82, mask_basis_7]
  rfl
private theorem mask_722 : fValue 722 = m722 := by
  rw [show 722 = Nat.xor 210 512 from rfl, fValue_xor, mask_210, mask_basis_9]
  rfl
private theorem mask_12 : fValue 12 = m12 := by
  rw [show 12 = Nat.xor 4 8 from rfl, fValue_xor, mask_basis_2, mask_basis_3]
  rfl
private theorem mask_19 : fValue 19 = m19 := by
  rw [show 19 = Nat.xor 3 16 from rfl, fValue_xor, mask_3, mask_basis_4]
  rfl
private theorem mask_83 : fValue 83 = m83 := by
  rw [show 83 = Nat.xor 19 64 from rfl, fValue_xor, mask_19, mask_basis_6]
  rfl
private theorem mask_140 : fValue 140 = m140 := by
  rw [show 140 = Nat.xor 12 128 from rfl, fValue_xor, mask_12, mask_basis_7]
  rfl
private theorem mask_396 : fValue 396 = m396 := by
  rw [show 396 = Nat.xor 140 256 from rfl, fValue_xor, mask_140, mask_basis_8]
  rfl
private theorem mask_44 : fValue 44 = m44 := by
  rw [show 44 = Nat.xor 12 32 from rfl, fValue_xor, mask_12, mask_basis_5]
  rfl
private theorem mask_108 : fValue 108 = m108 := by
  rw [show 108 = Nat.xor 44 64 from rfl, fValue_xor, mask_44, mask_basis_6]
  rfl
private theorem mask_236 : fValue 236 = m236 := by
  rw [show 236 = Nat.xor 108 128 from rfl, fValue_xor, mask_108, mask_basis_7]
  rfl
private theorem mask_492 : fValue 492 = m492 := by
  rw [show 492 = Nat.xor 236 256 from rfl, fValue_xor, mask_236, mask_basis_8]
  rfl
private theorem mask_88 : fValue 88 = m88 := by
  rw [show 88 = Nat.xor 24 64 from rfl, fValue_xor, mask_24, mask_basis_6]
  rfl
private theorem mask_600 : fValue 600 = m600 := by
  rw [show 600 = Nat.xor 88 512 from rfl, fValue_xor, mask_88, mask_basis_9]
  rfl
private theorem mask_20 : fValue 20 = m20 := by
  rw [show 20 = Nat.xor 4 16 from rfl, fValue_xor, mask_basis_2, mask_basis_4]
  rfl
private theorem mask_52 : fValue 52 = m52 := by
  rw [show 52 = Nat.xor 20 32 from rfl, fValue_xor, mask_20, mask_basis_5]
  rfl
private theorem mask_116 : fValue 116 = m116 := by
  rw [show 116 = Nat.xor 52 64 from rfl, fValue_xor, mask_52, mask_basis_6]
  rfl
private theorem mask_27 : fValue 27 = m27 := by
  rw [show 27 = Nat.xor 11 16 from rfl, fValue_xor, mask_11, mask_basis_4]
  rfl
private theorem mask_91 : fValue 91 = m91 := by
  rw [show 91 = Nat.xor 27 64 from rfl, fValue_xor, mask_27, mask_basis_6]
  rfl
private theorem mask_603 : fValue 603 = m603 := by
  rw [show 603 = Nat.xor 91 512 from rfl, fValue_xor, mask_91, mask_basis_9]
  rfl
private theorem decode_relation {a b c d : Vector ℕ 112}
    (h : packedMul a b = packedMul c d) :
    decodeRows a * decodeRows b = decodeRows c * decodeRows d :=
  (decode_packedMul a b).symm.trans ((congrArg decodeRows h).trans (decode_packedMul c d))
theorem conjugate_0_0 : n0 * (generators 0 : Model) * n0⁻¹ = fValue 247 := by
  have h : n0 * (generators 0 : Model) = m247 * n0 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n0, eval_generator, eval_m247] using decode_relation action_0_0
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_247]
theorem conjugate_0_1 : n0 * (generators 1 : Model) * n0⁻¹ = fValue 868 := by
  have h : n0 * (generators 1 : Model) = m868 * n0 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n0, eval_generator, eval_m868] using decode_relation action_0_1
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_868]
theorem conjugate_0_2 : n0 * (generators 2 : Model) * n0⁻¹ = fValue 24 := by
  have h : n0 * (generators 2 : Model) = m24 * n0 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n0, eval_generator, eval_m24] using decode_relation action_0_2
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_24]
theorem conjugate_0_3 : n0 * (generators 3 : Model) * n0⁻¹ = fValue 803 := by
  have h : n0 * (generators 3 : Model) = m803 * n0 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n0, eval_generator, eval_m803] using decode_relation action_0_3
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_803]
theorem conjugate_0_4 : n0 * (generators 4 : Model) * n0⁻¹ = fValue 807 := by
  have h : n0 * (generators 4 : Model) = m807 * n0 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n0, eval_generator, eval_m807] using decode_relation action_0_4
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_807]
theorem conjugate_0_5 : n0 * (generators 5 : Model) * n0⁻¹ = fValue 779 := by
  have h : n0 * (generators 5 : Model) = m779 * n0 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n0, eval_generator, eval_m779] using decode_relation action_0_5
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_779]
theorem conjugate_0_6 : n0 * (generators 6 : Model) * n0⁻¹ = fValue 897 := by
  have h : n0 * (generators 6 : Model) = m897 * n0 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n0, eval_generator, eval_m897] using decode_relation action_0_6
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_897]
theorem conjugate_0_7 : n0 * (generators 7 : Model) * n0⁻¹ = fValue 39 := by
  have h : n0 * (generators 7 : Model) = m39 * n0 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n0, eval_generator, eval_m39] using decode_relation action_0_7
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_39]
theorem conjugate_0_8 : n0 * (generators 8 : Model) * n0⁻¹ = fValue 502 := by
  have h : n0 * (generators 8 : Model) = m502 * n0 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n0, eval_generator, eval_m502] using decode_relation action_0_8
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_502]
theorem conjugate_0_9 : n0 * (generators 9 : Model) * n0⁻¹ = fValue 358 := by
  have h : n0 * (generators 9 : Model) = m358 * n0 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n0, eval_generator, eval_m358] using decode_relation action_0_9
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_358]
theorem conjugate_1_0 : n1 * (generators 0 : Model) * n1⁻¹ = fValue 746 := by
  have h : n1 * (generators 0 : Model) = m746 * n1 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n1, eval_generator, eval_m746] using decode_relation action_1_0
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_746]
theorem conjugate_1_1 : n1 * (generators 1 : Model) * n1⁻¹ = fValue 722 := by
  have h : n1 * (generators 1 : Model) = m722 * n1 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n1, eval_generator, eval_m722] using decode_relation action_1_1
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_722]
theorem conjugate_1_2 : n1 * (generators 2 : Model) * n1⁻¹ = fValue 12 := by
  have h : n1 * (generators 2 : Model) = m12 * n1 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n1, eval_generator, eval_m12] using decode_relation action_1_2
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_12]
theorem conjugate_1_3 : n1 * (generators 3 : Model) * n1⁻¹ = fValue 83 := by
  have h : n1 * (generators 3 : Model) = m83 * n1 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n1, eval_generator, eval_m83] using decode_relation action_1_3
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_83]
theorem conjugate_1_4 : n1 * (generators 4 : Model) * n1⁻¹ = fValue 868 := by
  have h : n1 * (generators 4 : Model) = m868 * n1 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n1, eval_generator, eval_m868] using decode_relation action_1_4
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_868]
theorem conjugate_1_5 : n1 * (generators 5 : Model) * n1⁻¹ = fValue 396 := by
  have h : n1 * (generators 5 : Model) = m396 * n1 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n1, eval_generator, eval_m396] using decode_relation action_1_5
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_396]
theorem conjugate_1_6 : n1 * (generators 6 : Model) * n1⁻¹ = fValue 492 := by
  have h : n1 * (generators 6 : Model) = m492 * n1 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n1, eval_generator, eval_m492] using decode_relation action_1_6
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_492]
theorem conjugate_1_7 : n1 * (generators 7 : Model) * n1⁻¹ = fValue 600 := by
  have h : n1 * (generators 7 : Model) = m600 * n1 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n1, eval_generator, eval_m600] using decode_relation action_1_7
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_600]
theorem conjugate_1_8 : n1 * (generators 8 : Model) * n1⁻¹ = fValue 116 := by
  have h : n1 * (generators 8 : Model) = m116 * n1 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n1, eval_generator, eval_m116] using decode_relation action_1_8
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_116]
theorem conjugate_1_9 : n1 * (generators 9 : Model) * n1⁻¹ = fValue 603 := by
  have h : n1 * (generators 9 : Model) = m603 * n1 := by
    apply toMatrix_injective
    simpa only [map_mul, eval_n1, eval_generator, eval_m603] using decode_relation action_1_9
  rw [h, mul_assoc, mul_inv_cancel, mul_one, mask_603]
end Janko4.LocalStructure.LinearFive.NativeNormalizer
