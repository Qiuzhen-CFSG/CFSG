module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftMatrixRelations
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftWords

/-!
# Evaluation of the corrected Figure 1/2 lifts

Shared list concatenations evaluate by homomorphism laws. The checked packed
products then identify the six representatives in the faithful native matrix
representation. All kernel corrections use the original eleven-bit coordinates.
-/

public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Theory.GroupTheory Cardinality KernelCount QuotientCount.Image
open KernelCount.Relations (eval_mul eval_inv representation_x representation_y decoded_product)
open Simplicity.Max1Fusion.KernelOrbits Janko4.GeneratorCertificates
open LiftWords LiftMatrices
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis
local notation "ρ" => representation matrixA_mul_self matrixB_pow_four

private theorem eval_append (a b : List (Fin 4)) :
    evalWord nativeAlphabet (a ++ b) = evalWord nativeAlphabet a * evalWord nativeAlphabet b := by
  induction a with
  | nil => simp only [List.nil_append, evalWord, one_mul]
  | cons i a ih => simp only [List.cons_append, evalWord, ih, mul_assoc]

private theorem eval_w0 : ρ (evalWord nativeAlphabet w0) = decodeRows xRows := by
  simpa [w0, evalWord, nativeAlphabet] using representation_x matrixA_mul_self matrixB_pow_four
private theorem eval_w1 : ρ (evalWord nativeAlphabet w1) = decodeRows yRows := by
  simpa [w1, evalWord, nativeAlphabet] using representation_y matrixA_mul_self matrixB_pow_four
private theorem eval_w2 : ρ (evalWord nativeAlphabet w2) = decodeRows xRows := by
  change ρ ((localX matrixA_mul_self matrixB_pow_four)⁻¹ * 1) = _
  rw [mul_one, inv_eq_of_mul_eq_one_left (localX_mul_self matrixA_mul_self matrixB_pow_four)]
  exact representation_x _ _
private theorem eval_w3 : ρ (evalWord nativeAlphabet w3) = decodeRows inverseYRows := by
  change ρ ((localY matrixA_mul_self matrixB_pow_four)⁻¹ * 1) = _
  rw [mul_one]
  exact eval_inv ρ (representation_y _ _) (by rw [decoded_product product_inverseY, decode_packedOne])
private theorem eval_w4 : ρ (evalWord nativeAlphabet w4) = decodeRows w4Rows := by
  rw [w4, eval_append]
  exact eval_mul ρ eval_w0 eval_w1 (decoded_product product_w4)
private theorem eval_w5 : ρ (evalWord nativeAlphabet w5) = decodeRows w5Rows := by
  rw [w5, eval_append]
  exact eval_mul ρ eval_w0 eval_w3 (decoded_product product_w5)
private theorem eval_w6 : ρ (evalWord nativeAlphabet w6) = decodeRows w6Rows := by
  rw [w6, eval_append]
  exact eval_mul ρ eval_w2 eval_w3 (decoded_product product_w6)
private theorem eval_w7 : ρ (evalWord nativeAlphabet w7) = decodeRows w7Rows := by
  rw [w7, eval_append]
  exact eval_mul ρ eval_w2 eval_w1 (decoded_product product_w7)
private theorem eval_w8 : ρ (evalWord nativeAlphabet w8) = decodeRows w8Rows := by
  rw [w8, eval_append]
  exact eval_mul ρ eval_w4 eval_w4 (decoded_product product_w8)
private theorem eval_w9 : ρ (evalWord nativeAlphabet w9) = decodeRows w9Rows := by
  rw [w9, eval_append]
  exact eval_mul ρ eval_w5 eval_w5 (decoded_product product_w9)
private theorem eval_w10 : ρ (evalWord nativeAlphabet w10) = decodeRows w10Rows := by
  rw [w10, eval_append]
  exact eval_mul ρ eval_w7 eval_w6 (decoded_product product_w10)
private theorem eval_w11 : ρ (evalWord nativeAlphabet w11) = decodeRows w11Rows := by
  rw [w11, eval_append]
  exact eval_mul ρ eval_w6 eval_w6 (decoded_product product_w11)
private theorem eval_w12 : ρ (evalWord nativeAlphabet w12) = decodeRows w12Rows := by
  rw [w12, eval_append]
  exact eval_mul ρ eval_w5 eval_w8 (decoded_product product_w12)
private theorem eval_w13 : ρ (evalWord nativeAlphabet w13) = decodeRows w13Rows := by
  rw [w13, eval_append]
  exact eval_mul ρ eval_w7 eval_w7 (decoded_product product_w13)
private theorem eval_w14 : ρ (evalWord nativeAlphabet w14) = decodeRows w14Rows := by
  rw [w14, eval_append]
  exact eval_mul ρ eval_w4 eval_w9 (decoded_product product_w14)
private theorem eval_w15 : ρ (evalWord nativeAlphabet w15) = decodeRows w15Rows := by
  rw [w15, eval_append]
  exact eval_mul ρ eval_w10 eval_w10 (decoded_product product_w15)
private theorem eval_w16 : ρ (evalWord nativeAlphabet w16) = decodeRows w16Rows := by
  rw [w16, eval_append]
  exact eval_mul ρ eval_w5 eval_w14 (decoded_product product_w16)
private theorem eval_w17 : ρ (evalWord nativeAlphabet w17) = decodeRows w17Rows := by
  rw [w17, eval_append]
  exact eval_mul ρ eval_w4 eval_w12 (decoded_product product_w17)
private theorem eval_w18 : ρ (evalWord nativeAlphabet w18) = decodeRows w18Rows := by
  rw [w18, eval_append]
  exact eval_mul ρ eval_w10 eval_w7 (decoded_product product_w18)
private theorem eval_w19 : ρ (evalWord nativeAlphabet w19) = decodeRows w19Rows := by
  rw [w19, eval_append]
  exact eval_mul ρ eval_w17 eval_w8 (decoded_product product_w19)
private theorem eval_w20 : ρ (evalWord nativeAlphabet w20) = decodeRows w20Rows := by
  rw [w20, eval_append]
  exact eval_mul ρ eval_w11 eval_w6 (decoded_product product_w20)
private theorem eval_w21 : ρ (evalWord nativeAlphabet w21) = decodeRows w21Rows := by
  rw [w21, eval_append]
  exact eval_mul ρ eval_w14 eval_w12 (decoded_product product_w21)
private theorem eval_w22 : ρ (evalWord nativeAlphabet w22) = decodeRows w22Rows := by
  rw [w22, eval_append]
  exact eval_mul ρ eval_w10 eval_w6 (decoded_product product_w22)
private theorem eval_w23 : ρ (evalWord nativeAlphabet w23) = decodeRows w23Rows := by
  rw [w23, eval_append]
  exact eval_mul ρ eval_w13 eval_w13 (decoded_product product_w23)
private theorem eval_w24 : ρ (evalWord nativeAlphabet w24) = decodeRows w24Rows := by
  rw [w24, eval_append]
  exact eval_mul ρ eval_w5 eval_w4 (decoded_product product_w24)
private theorem eval_w25 : ρ (evalWord nativeAlphabet w25) = decodeRows w25Rows := by
  rw [w25, eval_append]
  exact eval_mul ρ eval_w11 eval_w11 (decoded_product product_w25)
private theorem eval_w26 : ρ (evalWord nativeAlphabet w26) = decodeRows w26Rows := by
  rw [w26, eval_append]
  exact eval_mul ρ eval_w18 eval_w18 (decoded_product product_w26)
private theorem eval_w27 : ρ (evalWord nativeAlphabet w27) = decodeRows w27Rows := by
  rw [w27, eval_append]
  exact eval_mul ρ eval_w19 eval_w15 (decoded_product product_w27)
private theorem eval_w28 : ρ (evalWord nativeAlphabet w28) = decodeRows w28Rows := by
  rw [w28, eval_append]
  exact eval_mul ρ eval_w27 eval_w3 (decoded_product product_w28)
private theorem eval_w29 : ρ (evalWord nativeAlphabet w29) = decodeRows w29Rows := by
  rw [w29, eval_append]
  exact eval_mul ρ eval_w28 eval_w21 (decoded_product product_w29)
private theorem eval_w30 : ρ (evalWord nativeAlphabet w30) = decodeRows w30Rows := by
  rw [w30, eval_append]
  exact eval_mul ρ eval_w29 eval_w4 (decoded_product product_w30)
private theorem eval_w31 : ρ (evalWord nativeAlphabet w31) = decodeRows w31Rows := by
  rw [w31, eval_append]
  exact eval_mul ρ eval_w6 eval_w7 (decoded_product product_w31)
private theorem eval_w32 : ρ (evalWord nativeAlphabet w32) = decodeRows w32Rows := by
  rw [w32, eval_append]
  exact eval_mul ρ eval_w8 eval_w8 (decoded_product product_w32)
private theorem eval_w33 : ρ (evalWord nativeAlphabet w33) = decodeRows w33Rows := by
  rw [w33, eval_append]
  exact eval_mul ρ eval_w10 eval_w20 (decoded_product product_w33)
private theorem eval_w34 : ρ (evalWord nativeAlphabet w34) = decodeRows w34Rows := by
  rw [w34, eval_append]
  exact eval_mul ρ eval_w9 eval_w9 (decoded_product product_w34)
private theorem eval_w35 : ρ (evalWord nativeAlphabet w35) = decodeRows w35Rows := by
  rw [w35, eval_append]
  exact eval_mul ρ eval_w10 eval_w11 (decoded_product product_w35)
private theorem eval_w36 : ρ (evalWord nativeAlphabet w36) = decodeRows w36Rows := by
  rw [w36, eval_append]
  exact eval_mul ρ eval_w23 eval_w1 (decoded_product product_w36)
private theorem eval_w37 : ρ (evalWord nativeAlphabet w37) = decodeRows w37Rows := by
  rw [w37, eval_append]
  exact eval_mul ρ eval_w7 eval_w1 (decoded_product product_w37)
private theorem eval_w38 : ρ (evalWord nativeAlphabet w38) = decodeRows w38Rows := by
  rw [w38, eval_append]
  exact eval_mul ρ eval_w24 eval_w16 (decoded_product product_w38)
private theorem eval_w39 : ρ (evalWord nativeAlphabet w39) = decodeRows w39Rows := by
  rw [w39, eval_append]
  exact eval_mul ρ eval_w21 eval_w30 (decoded_product product_w39)
private theorem eval_w40 : ρ (evalWord nativeAlphabet w40) = decodeRows w40Rows := by
  rw [w40, eval_append]
  exact eval_mul ρ eval_w22 eval_w15 (decoded_product product_w40)
private theorem eval_w41 : ρ (evalWord nativeAlphabet w41) = decodeRows w41Rows := by
  rw [w41, eval_append]
  exact eval_mul ρ eval_w31 eval_w15 (decoded_product product_w41)
private theorem eval_w42 : ρ (evalWord nativeAlphabet w42) = decodeRows w42Rows := by
  rw [w42, eval_append]
  exact eval_mul ρ eval_w4 eval_w1 (decoded_product product_w42)
private theorem eval_w43 : ρ (evalWord nativeAlphabet w43) = decodeRows w43Rows := by
  rw [w43, eval_append]
  exact eval_mul ρ eval_w8 eval_w9 (decoded_product product_w43)
private theorem eval_w44 : ρ (evalWord nativeAlphabet w44) = decodeRows w44Rows := by
  rw [w44, eval_append]
  exact eval_mul ρ eval_w10 eval_w36 (decoded_product product_w44)
private theorem eval_w45 : ρ (evalWord nativeAlphabet w45) = decodeRows w45Rows := by
  rw [w45, eval_append]
  exact eval_mul ρ eval_w16 eval_w17 (decoded_product product_w45)
private theorem eval_w46 : ρ (evalWord nativeAlphabet w46) = decodeRows w46Rows := by
  rw [w46, eval_append]
  exact eval_mul ρ eval_w45 eval_w14 (decoded_product product_w46)
private theorem eval_w47 : ρ (evalWord nativeAlphabet w47) = decodeRows w47Rows := by
  rw [w47, eval_append]
  exact eval_mul ρ eval_w38 eval_w5 (decoded_product product_w47)
private theorem eval_w48 : ρ (evalWord nativeAlphabet w48) = decodeRows w48Rows := by
  rw [w48, eval_append]
  exact eval_mul ρ eval_w12 eval_w32 (decoded_product product_w48)
private theorem eval_w49 : ρ (evalWord nativeAlphabet w49) = decodeRows w49Rows := by
  rw [w49, eval_append]
  exact eval_mul ρ eval_w13 eval_w18 (decoded_product product_w49)
private theorem eval_w50 : ρ (evalWord nativeAlphabet w50) = decodeRows w50Rows := by
  rw [w50, eval_append]
  exact eval_mul ρ eval_w41 eval_w6 (decoded_product product_w50)
private theorem eval_w51 : ρ (evalWord nativeAlphabet w51) = decodeRows w51Rows := by
  rw [w51, eval_append]
  exact eval_mul ρ eval_w50 eval_w15 (decoded_product product_w51)
private theorem eval_w52 : ρ (evalWord nativeAlphabet w52) = decodeRows w52Rows := by
  rw [w52, eval_append]
  exact eval_mul ρ eval_w51 eval_w7 (decoded_product product_w52)
private theorem eval_w53 : ρ (evalWord nativeAlphabet w53) = decodeRows w53Rows := by
  rw [w53, eval_append]
  exact eval_mul ρ eval_w52 eval_w26 (decoded_product product_w53)
private theorem eval_w54 : ρ (evalWord nativeAlphabet w54) = decodeRows w54Rows := by
  rw [w54, eval_append]
  exact eval_mul ρ eval_w53 eval_w16 (decoded_product product_w54)
private theorem eval_w55 : ρ (evalWord nativeAlphabet w55) = decodeRows w55Rows := by
  rw [w55, eval_append]
  exact eval_mul ρ eval_w54 eval_w8 (decoded_product product_w55)
private theorem eval_w56 : ρ (evalWord nativeAlphabet w56) = decodeRows w56Rows := by
  rw [w56, eval_append]
  exact eval_mul ρ eval_w55 eval_w14 (decoded_product product_w56)
private theorem eval_w57 : ρ (evalWord nativeAlphabet w57) = decodeRows w57Rows := by
  rw [w57, eval_append]
  exact eval_mul ρ eval_w56 eval_w39 (decoded_product product_w57)
private theorem eval_w58 : ρ (evalWord nativeAlphabet w58) = decodeRows w58Rows := by
  rw [w58, eval_append]
  exact eval_mul ρ eval_w12 eval_w4 (decoded_product product_w58)
private theorem eval_w59 : ρ (evalWord nativeAlphabet w59) = decodeRows w59Rows := by
  rw [w59, eval_append]
  exact eval_mul ρ eval_w4 eval_w16 (decoded_product product_w59)
private theorem eval_w60 : ρ (evalWord nativeAlphabet w60) = decodeRows w60Rows := by
  rw [w60, eval_append]
  exact eval_mul ρ eval_w9 eval_w5 (decoded_product product_w60)
private theorem eval_w61 : ρ (evalWord nativeAlphabet w61) = decodeRows w61Rows := by
  rw [w61, eval_append]
  exact eval_mul ρ eval_w4 eval_w5 (decoded_product product_w61)
private theorem eval_w62 : ρ (evalWord nativeAlphabet w62) = decodeRows w62Rows := by
  rw [w62, eval_append]
  exact eval_mul ρ eval_w6 eval_w10 (decoded_product product_w62)
private theorem eval_w63 : ρ (evalWord nativeAlphabet w63) = decodeRows w63Rows := by
  rw [w63, eval_append]
  exact eval_mul ρ eval_w24 eval_w25 (decoded_product product_w63)
private theorem eval_w64 : ρ (evalWord nativeAlphabet w64) = decodeRows w64Rows := by
  rw [w64, eval_append]
  exact eval_mul ρ eval_w16 eval_w12 (decoded_product product_w64)
private theorem eval_w65 : ρ (evalWord nativeAlphabet w65) = decodeRows w65Rows := by
  rw [w65, eval_append]
  exact eval_mul ρ eval_w64 eval_w30 (decoded_product product_w65)
private theorem eval_w66 : ρ (evalWord nativeAlphabet w66) = decodeRows w66Rows := by
  rw [w66, eval_append]
  exact eval_mul ρ eval_w10 eval_w2 (decoded_product product_w66)
private theorem eval_w67 : ρ (evalWord nativeAlphabet w67) = decodeRows w67Rows := by
  rw [w67, eval_append]
  exact eval_mul ρ eval_w66 eval_w13 (decoded_product product_w67)
private theorem eval_w68 : ρ (evalWord nativeAlphabet w68) = decodeRows w68Rows := by
  rw [w68, eval_append]
  exact eval_mul ρ eval_w67 eval_w7 (decoded_product product_w68)
private theorem eval_w69 : ρ (evalWord nativeAlphabet w69) = decodeRows w69Rows := by
  rw [w69, eval_append]
  exact eval_mul ρ eval_w68 eval_w35 (decoded_product product_w69)
private theorem eval_w70 : ρ (evalWord nativeAlphabet w70) = decodeRows w70Rows := by
  rw [w70, eval_append]
  exact eval_mul ρ eval_w69 eval_w22 (decoded_product product_w70)
private theorem eval_w71 : ρ (evalWord nativeAlphabet w71) = decodeRows w71Rows := by
  rw [w71, eval_append]
  exact eval_mul ρ eval_w70 eval_w44 (decoded_product product_w71)
private theorem eval_w72 : ρ (evalWord nativeAlphabet w72) = decodeRows w72Rows := by
  rw [w72, eval_append]
  exact eval_mul ρ eval_w71 eval_w46 (decoded_product product_w72)
private theorem eval_w73 : ρ (evalWord nativeAlphabet w73) = decodeRows w73Rows := by
  rw [w73, eval_append]
  exact eval_mul ρ eval_w72 eval_w8 (decoded_product product_w73)
private theorem eval_w74 : ρ (evalWord nativeAlphabet w74) = decodeRows w74Rows := by
  rw [w74, eval_append]
  exact eval_mul ρ eval_w73 eval_w23 (decoded_product product_w74)
private theorem eval_w75 : ρ (evalWord nativeAlphabet w75) = decodeRows w75Rows := by
  rw [w75, eval_append]
  exact eval_mul ρ eval_w74 eval_w13 (decoded_product product_w75)
private theorem eval_w76 : ρ (evalWord nativeAlphabet w76) = decodeRows w76Rows := by
  rw [w76, eval_append]
  exact eval_mul ρ eval_w75 eval_w37 (decoded_product product_w76)
private theorem eval_w77 : ρ (evalWord nativeAlphabet w77) = decodeRows w77Rows := by
  rw [w77, eval_append]
  exact eval_mul ρ eval_w76 eval_w47 (decoded_product product_w77)
private theorem eval_w78 : ρ (evalWord nativeAlphabet w78) = decodeRows w78Rows := by
  rw [w78, eval_append]
  exact eval_mul ρ eval_w77 eval_w19 (decoded_product product_w78)
private theorem eval_w79 : ρ (evalWord nativeAlphabet w79) = decodeRows w79Rows := by
  rw [w79, eval_append]
  exact eval_mul ρ eval_w78 eval_w48 (decoded_product product_w79)
private theorem eval_w80 : ρ (evalWord nativeAlphabet w80) = decodeRows w80Rows := by
  rw [w80, eval_append]
  exact eval_mul ρ eval_w79 eval_w0 (decoded_product product_w80)
private theorem eval_w81 : ρ (evalWord nativeAlphabet w81) = decodeRows w81Rows := by
  rw [w81, eval_append]
  exact eval_mul ρ eval_w80 eval_w48 (decoded_product product_w81)
private theorem eval_w82 : ρ (evalWord nativeAlphabet w82) = decodeRows w82Rows := by
  rw [w82, eval_append]
  exact eval_mul ρ eval_w81 eval_w5 (decoded_product product_w82)
private theorem eval_w83 : ρ (evalWord nativeAlphabet w83) = decodeRows w83Rows := by
  rw [w83, eval_append]
  exact eval_mul ρ eval_w82 eval_w20 (decoded_product product_w83)
private theorem eval_w84 : ρ (evalWord nativeAlphabet w84) = decodeRows w84Rows := by
  rw [w84, eval_append]
  exact eval_mul ρ eval_w83 eval_w26 (decoded_product product_w84)
private theorem eval_w85 : ρ (evalWord nativeAlphabet w85) = decodeRows w85Rows := by
  rw [w85, eval_append]
  exact eval_mul ρ eval_w84 eval_w15 (decoded_product product_w85)
private theorem eval_w86 : ρ (evalWord nativeAlphabet w86) = decodeRows w86Rows := by
  rw [w86, eval_append]
  exact eval_mul ρ eval_w85 eval_w12 (decoded_product product_w86)
private theorem eval_w87 : ρ (evalWord nativeAlphabet w87) = decodeRows w87Rows := by
  rw [w87, eval_append]
  exact eval_mul ρ eval_w86 eval_w38 (decoded_product product_w87)
private theorem eval_w88 : ρ (evalWord nativeAlphabet w88) = decodeRows w88Rows := by
  rw [w88, eval_append]
  exact eval_mul ρ eval_w87 eval_w39 (decoded_product product_w88)
private theorem eval_w89 : ρ (evalWord nativeAlphabet w89) = decodeRows w89Rows := by
  rw [w89, eval_append]
  exact eval_mul ρ eval_w40 eval_w25 (decoded_product product_w89)
private theorem eval_w90 : ρ (evalWord nativeAlphabet w90) = decodeRows w90Rows := by
  rw [w90, eval_append]
  exact eval_mul ρ eval_w89 eval_w20 (decoded_product product_w90)
private theorem eval_w91 : ρ (evalWord nativeAlphabet w91) = decodeRows w91Rows := by
  rw [w91, eval_append]
  exact eval_mul ρ eval_w90 eval_w33 (decoded_product product_w91)
private theorem eval_w92 : ρ (evalWord nativeAlphabet w92) = decodeRows w92Rows := by
  rw [w92, eval_append]
  exact eval_mul ρ eval_w91 eval_w37 (decoded_product product_w92)
private theorem eval_w93 : ρ (evalWord nativeAlphabet w93) = decodeRows w93Rows := by
  rw [w93, eval_append]
  exact eval_mul ρ eval_w92 eval_w49 (decoded_product product_w93)
private theorem eval_w94 : ρ (evalWord nativeAlphabet w94) = decodeRows w94Rows := by
  rw [w94, eval_append]
  exact eval_mul ρ eval_w93 eval_w8 (decoded_product product_w94)
private theorem eval_w95 : ρ (evalWord nativeAlphabet w95) = decodeRows w95Rows := by
  rw [w95, eval_append]
  exact eval_mul ρ eval_w94 eval_w19 (decoded_product product_w95)
private theorem eval_w96 : ρ (evalWord nativeAlphabet w96) = decodeRows w96Rows := by
  rw [w96, eval_append]
  exact eval_mul ρ eval_w95 eval_w19 (decoded_product product_w96)
private theorem eval_w97 : ρ (evalWord nativeAlphabet w97) = decodeRows w97Rows := by
  rw [w97, eval_append]
  exact eval_mul ρ eval_w96 eval_w8 (decoded_product product_w97)
private theorem eval_w98 : ρ (evalWord nativeAlphabet w98) = decodeRows w98Rows := by
  rw [w98, eval_append]
  exact eval_mul ρ eval_w97 eval_w5 (decoded_product product_w98)
private theorem eval_w99 : ρ (evalWord nativeAlphabet w99) = decodeRows w99Rows := by
  rw [w99, eval_append]
  exact eval_mul ρ eval_w98 eval_w23 (decoded_product product_w99)
private theorem eval_w100 : ρ (evalWord nativeAlphabet w100) = decodeRows w100Rows := by
  rw [w100, eval_append]
  exact eval_mul ρ eval_w99 eval_w15 (decoded_product product_w100)
private theorem eval_w101 : ρ (evalWord nativeAlphabet w101) = decodeRows w101Rows := by
  rw [w101, eval_append]
  exact eval_mul ρ eval_w100 eval_w33 (decoded_product product_w101)
private theorem eval_w102 : ρ (evalWord nativeAlphabet w102) = decodeRows w102Rows := by
  rw [w102, eval_append]
  exact eval_mul ρ eval_w101 eval_w15 (decoded_product product_w102)
private theorem eval_w103 : ρ (evalWord nativeAlphabet w103) = decodeRows w103Rows := by
  rw [w103, eval_append]
  exact eval_mul ρ eval_w102 eval_w31 (decoded_product product_w103)
private theorem eval_w104 : ρ (evalWord nativeAlphabet w104) = decodeRows w104Rows := by
  rw [w104, eval_append]
  exact eval_mul ρ eval_w103 eval_w2 (decoded_product product_w104)
private theorem eval_w105 : ρ (evalWord nativeAlphabet w105) = decodeRows w105Rows := by
  rw [w105, eval_append]
  exact eval_mul ρ eval_w104 eval_w57 (decoded_product product_w105)
private theorem eval_w106 : ρ (evalWord nativeAlphabet w106) = decodeRows w106Rows := by
  rw [w106, eval_append]
  exact eval_mul ρ eval_w40 eval_w11 (decoded_product product_w106)
private theorem eval_w107 : ρ (evalWord nativeAlphabet w107) = decodeRows w107Rows := by
  rw [w107, eval_append]
  exact eval_mul ρ eval_w106 eval_w12 (decoded_product product_w107)
private theorem eval_w108 : ρ (evalWord nativeAlphabet w108) = decodeRows w108Rows := by
  rw [w108, eval_append]
  exact eval_mul ρ eval_w107 eval_w9 (decoded_product product_w108)
private theorem eval_w109 : ρ (evalWord nativeAlphabet w109) = decodeRows w109Rows := by
  rw [w109, eval_append]
  exact eval_mul ρ eval_w108 eval_w32 (decoded_product product_w109)
private theorem eval_w110 : ρ (evalWord nativeAlphabet w110) = decodeRows w110Rows := by
  rw [w110, eval_append]
  exact eval_mul ρ eval_w109 eval_w58 (decoded_product product_w110)
private theorem eval_w111 : ρ (evalWord nativeAlphabet w111) = decodeRows w111Rows := by
  rw [w111, eval_append]
  exact eval_mul ρ eval_w110 eval_w11 (decoded_product product_w111)
private theorem eval_w112 : ρ (evalWord nativeAlphabet w112) = decodeRows w112Rows := by
  rw [w112, eval_append]
  exact eval_mul ρ eval_w111 eval_w22 (decoded_product product_w112)
private theorem eval_w113 : ρ (evalWord nativeAlphabet w113) = decodeRows w113Rows := by
  rw [w113, eval_append]
  exact eval_mul ρ eval_w112 eval_w35 (decoded_product product_w113)
private theorem eval_w114 : ρ (evalWord nativeAlphabet w114) = decodeRows w114Rows := by
  rw [w114, eval_append]
  exact eval_mul ρ eval_w113 eval_w10 (decoded_product product_w114)
private theorem eval_w115 : ρ (evalWord nativeAlphabet w115) = decodeRows w115Rows := by
  rw [w115, eval_append]
  exact eval_mul ρ eval_w114 eval_w34 (decoded_product product_w115)
private theorem eval_w116 : ρ (evalWord nativeAlphabet w116) = decodeRows w116Rows := by
  rw [w116, eval_append]
  exact eval_mul ρ eval_w115 eval_w9 (decoded_product product_w116)
private theorem eval_w117 : ρ (evalWord nativeAlphabet w117) = decodeRows w117Rows := by
  rw [w117, eval_append]
  exact eval_mul ρ eval_w116 eval_w42 (decoded_product product_w117)
private theorem eval_w118 : ρ (evalWord nativeAlphabet w118) = decodeRows w118Rows := by
  rw [w118, eval_append]
  exact eval_mul ρ eval_w117 eval_w33 (decoded_product product_w118)
private theorem eval_w119 : ρ (evalWord nativeAlphabet w119) = decodeRows w119Rows := by
  rw [w119, eval_append]
  exact eval_mul ρ eval_w118 eval_w7 (decoded_product product_w119)
private theorem eval_w120 : ρ (evalWord nativeAlphabet w120) = decodeRows w120Rows := by
  rw [w120, eval_append]
  exact eval_mul ρ eval_w119 eval_w22 (decoded_product product_w120)
private theorem eval_w121 : ρ (evalWord nativeAlphabet w121) = decodeRows w121Rows := by
  rw [w121, eval_append]
  exact eval_mul ρ eval_w120 eval_w22 (decoded_product product_w121)
private theorem eval_w122 : ρ (evalWord nativeAlphabet w122) = decodeRows w122Rows := by
  rw [w122, eval_append]
  exact eval_mul ρ eval_w121 eval_w7 (decoded_product product_w122)
private theorem eval_w123 : ρ (evalWord nativeAlphabet w123) = decodeRows w123Rows := by
  rw [w123, eval_append]
  exact eval_mul ρ eval_w122 eval_w59 (decoded_product product_w123)
private theorem eval_w124 : ρ (evalWord nativeAlphabet w124) = decodeRows w124Rows := by
  rw [w124, eval_append]
  exact eval_mul ρ eval_w123 eval_w24 (decoded_product product_w124)
private theorem eval_w125 : ρ (evalWord nativeAlphabet w125) = decodeRows w125Rows := by
  rw [w125, eval_append]
  exact eval_mul ρ eval_w124 eval_w57 (decoded_product product_w125)
private theorem eval_w126 : ρ (evalWord nativeAlphabet w126) = decodeRows w126Rows := by
  rw [w126, eval_append]
  exact eval_mul ρ eval_w25 eval_w37 (decoded_product product_w126)
private theorem eval_w127 : ρ (evalWord nativeAlphabet w127) = decodeRows w127Rows := by
  rw [w127, eval_append]
  exact eval_mul ρ eval_w126 eval_w60 (decoded_product product_w127)
private theorem eval_w128 : ρ (evalWord nativeAlphabet w128) = decodeRows w128Rows := by
  rw [w128, eval_append]
  exact eval_mul ρ eval_w127 eval_w3 (decoded_product product_w128)
private theorem eval_w129 : ρ (evalWord nativeAlphabet w129) = decodeRows w129Rows := by
  rw [w129, eval_append]
  exact eval_mul ρ eval_w128 eval_w26 (decoded_product product_w129)
private theorem eval_w130 : ρ (evalWord nativeAlphabet w130) = decodeRows w130Rows := by
  rw [w130, eval_append]
  exact eval_mul ρ eval_w129 eval_w18 (decoded_product product_w130)
private theorem eval_w131 : ρ (evalWord nativeAlphabet w131) = decodeRows w131Rows := by
  rw [w131, eval_append]
  exact eval_mul ρ eval_w130 eval_w1 (decoded_product product_w131)
private theorem eval_w132 : ρ (evalWord nativeAlphabet w132) = decodeRows w132Rows := by
  rw [w132, eval_append]
  exact eval_mul ρ eval_w131 eval_w9 (decoded_product product_w132)
private theorem eval_w133 : ρ (evalWord nativeAlphabet w133) = decodeRows w133Rows := by
  rw [w133, eval_append]
  exact eval_mul ρ eval_w132 eval_w8 (decoded_product product_w133)
private theorem eval_w134 : ρ (evalWord nativeAlphabet w134) = decodeRows w134Rows := by
  rw [w134, eval_append]
  exact eval_mul ρ eval_w133 eval_w59 (decoded_product product_w134)
private theorem eval_w135 : ρ (evalWord nativeAlphabet w135) = decodeRows w135Rows := by
  rw [w135, eval_append]
  exact eval_mul ρ eval_w134 eval_w9 (decoded_product product_w135)
private theorem eval_w136 : ρ (evalWord nativeAlphabet w136) = decodeRows w136Rows := by
  rw [w136, eval_append]
  exact eval_mul ρ eval_w135 eval_w14 (decoded_product product_w136)
private theorem eval_w137 : ρ (evalWord nativeAlphabet w137) = decodeRows w137Rows := by
  rw [w137, eval_append]
  exact eval_mul ρ eval_w136 eval_w9 (decoded_product product_w137)
private theorem eval_w138 : ρ (evalWord nativeAlphabet w138) = decodeRows w138Rows := by
  rw [w138, eval_append]
  exact eval_mul ρ eval_w137 eval_w61 (decoded_product product_w138)
private theorem eval_w139 : ρ (evalWord nativeAlphabet w139) = decodeRows w139Rows := by
  rw [w139, eval_append]
  exact eval_mul ρ eval_w138 eval_w0 (decoded_product product_w139)
private theorem eval_w140 : ρ (evalWord nativeAlphabet w140) = decodeRows w140Rows := by
  rw [w140, eval_append]
  exact eval_mul ρ eval_w139 eval_w34 (decoded_product product_w140)
private theorem eval_w141 : ρ (evalWord nativeAlphabet w141) = decodeRows w141Rows := by
  rw [w141, eval_append]
  exact eval_mul ρ eval_w140 eval_w43 (decoded_product product_w141)
private theorem eval_w142 : ρ (evalWord nativeAlphabet w142) = decodeRows w142Rows := by
  rw [w142, eval_append]
  exact eval_mul ρ eval_w141 eval_w3 (decoded_product product_w142)
private theorem eval_w143 : ρ (evalWord nativeAlphabet w143) = decodeRows w143Rows := by
  rw [w143, eval_append]
  exact eval_mul ρ eval_w142 eval_w41 (decoded_product product_w143)
private theorem eval_w144 : ρ (evalWord nativeAlphabet w144) = decodeRows w144Rows := by
  rw [w144, eval_append]
  exact eval_mul ρ eval_w143 eval_w32 (decoded_product product_w144)
private theorem eval_w145 : ρ (evalWord nativeAlphabet w145) = decodeRows w145Rows := by
  rw [w145, eval_append]
  exact eval_mul ρ eval_w144 eval_w9 (decoded_product product_w145)
private theorem eval_w146 : ρ (evalWord nativeAlphabet w146) = decodeRows w146Rows := by
  rw [w146, eval_append]
  exact eval_mul ρ eval_w145 eval_w16 (decoded_product product_w146)
private theorem eval_w147 : ρ (evalWord nativeAlphabet w147) = decodeRows w147Rows := by
  rw [w147, eval_append]
  exact eval_mul ρ eval_w146 eval_w61 (decoded_product product_w147)
private theorem eval_w148 : ρ (evalWord nativeAlphabet w148) = decodeRows w148Rows := by
  rw [w148, eval_append]
  exact eval_mul ρ eval_w147 eval_w3 (decoded_product product_w148)
private theorem eval_w149 : ρ (evalWord nativeAlphabet w149) = decodeRows w149Rows := by
  rw [w149, eval_append]
  exact eval_mul ρ eval_w148 eval_w11 (decoded_product product_w149)
private theorem eval_w150 : ρ (evalWord nativeAlphabet w150) = decodeRows w150Rows := by
  rw [w150, eval_append]
  exact eval_mul ρ eval_w149 eval_w49 (decoded_product product_w150)
private theorem eval_w151 : ρ (evalWord nativeAlphabet w151) = decodeRows w151Rows := by
  rw [w151, eval_append]
  exact eval_mul ρ eval_w150 eval_w1 (decoded_product product_w151)
private theorem eval_w152 : ρ (evalWord nativeAlphabet w152) = decodeRows w152Rows := by
  rw [w152, eval_append]
  exact eval_mul ρ eval_w151 eval_w16 (decoded_product product_w152)
private theorem eval_w153 : ρ (evalWord nativeAlphabet w153) = decodeRows w153Rows := by
  rw [w153, eval_append]
  exact eval_mul ρ eval_w152 eval_w20 (decoded_product product_w153)
private theorem eval_w154 : ρ (evalWord nativeAlphabet w154) = decodeRows w154Rows := by
  rw [w154, eval_append]
  exact eval_mul ρ eval_w153 eval_w35 (decoded_product product_w154)
private theorem eval_w155 : ρ (evalWord nativeAlphabet w155) = decodeRows w155Rows := by
  rw [w155, eval_append]
  exact eval_mul ρ eval_w154 eval_w13 (decoded_product product_w155)
private theorem eval_w156 : ρ (evalWord nativeAlphabet w156) = decodeRows w156Rows := by
  rw [w156, eval_append]
  exact eval_mul ρ eval_w155 eval_w10 (decoded_product product_w156)
private theorem eval_w157 : ρ (evalWord nativeAlphabet w157) = decodeRows w157Rows := by
  rw [w157, eval_append]
  exact eval_mul ρ eval_w156 eval_w13 (decoded_product product_w157)
private theorem eval_w158 : ρ (evalWord nativeAlphabet w158) = decodeRows w158Rows := by
  rw [w158, eval_append]
  exact eval_mul ρ eval_w1 eval_w62 (decoded_product product_w158)
private theorem eval_w159 : ρ (evalWord nativeAlphabet w159) = decodeRows w159Rows := by
  rw [w159, eval_append]
  exact eval_mul ρ eval_w158 eval_w3 (decoded_product product_w159)
private theorem eval_w160 : ρ (evalWord nativeAlphabet w160) = decodeRows w160Rows := by
  rw [w160, eval_append]
  exact eval_mul ρ eval_w159 eval_w43 (decoded_product product_w160)
private theorem eval_w161 : ρ (evalWord nativeAlphabet w161) = decodeRows w161Rows := by
  rw [w161, eval_append]
  exact eval_mul ρ eval_w160 eval_w8 (decoded_product product_w161)
private theorem eval_w162 : ρ (evalWord nativeAlphabet w162) = decodeRows w162Rows := by
  rw [w162, eval_append]
  exact eval_mul ρ eval_w161 eval_w63 (decoded_product product_w162)
private theorem eval_w163 : ρ (evalWord nativeAlphabet w163) = decodeRows w163Rows := by
  rw [w163, eval_append]
  exact eval_mul ρ eval_w162 eval_w11 (decoded_product product_w163)
private theorem eval_w164 : ρ (evalWord nativeAlphabet w164) = decodeRows w164Rows := by
  rw [w164, eval_append]
  exact eval_mul ρ eval_w163 eval_w7 (decoded_product product_w164)
private theorem eval_w165 : ρ (evalWord nativeAlphabet w165) = decodeRows w165Rows := by
  rw [w165, eval_append]
  exact eval_mul ρ eval_w164 eval_w2 (decoded_product product_w165)
private theorem eval_w166 : ρ (evalWord nativeAlphabet w166) = decodeRows w166Rows := by
  rw [w166, eval_append]
  exact eval_mul ρ eval_w165 eval_w36 (decoded_product product_w166)
private theorem eval_w167 : ρ (evalWord nativeAlphabet w167) = decodeRows w167Rows := by
  rw [w167, eval_append]
  exact eval_mul ρ eval_w166 eval_w46 (decoded_product product_w167)
private theorem eval_w168 : ρ (evalWord nativeAlphabet w168) = decodeRows w168Rows := by
  rw [w168, eval_append]
  exact eval_mul ρ eval_w167 eval_w42 (decoded_product product_w168)
private theorem eval_w169 : ρ (evalWord nativeAlphabet w169) = decodeRows w169Rows := by
  rw [w169, eval_append]
  exact eval_mul ρ eval_w168 eval_w31 (decoded_product product_w169)
private theorem eval_w170 : ρ (evalWord nativeAlphabet w170) = decodeRows w170Rows := by
  rw [w170, eval_append]
  exact eval_mul ρ eval_w169 eval_w44 (decoded_product product_w170)
private theorem eval_w171 : ρ (evalWord nativeAlphabet w171) = decodeRows w171Rows := by
  rw [w171, eval_append]
  exact eval_mul ρ eval_w170 eval_w9 (decoded_product product_w171)
private theorem eval_w172 : ρ (evalWord nativeAlphabet w172) = decodeRows w172Rows := by
  rw [w172, eval_append]
  exact eval_mul ρ eval_w171 eval_w63 (decoded_product product_w172)
private theorem eval_w173 : ρ (evalWord nativeAlphabet w173) = decodeRows w173Rows := by
  rw [w173, eval_append]
  exact eval_mul ρ eval_w172 eval_w7 (decoded_product product_w173)
private theorem eval_w174 : ρ (evalWord nativeAlphabet w174) = decodeRows w174Rows := by
  rw [w174, eval_append]
  exact eval_mul ρ eval_w173 eval_w15 (decoded_product product_w174)
private theorem eval_w175 : ρ (evalWord nativeAlphabet w175) = decodeRows w175Rows := by
  rw [w175, eval_append]
  exact eval_mul ρ eval_w174 eval_w25 (decoded_product product_w175)
private theorem eval_w176 : ρ (evalWord nativeAlphabet w176) = decodeRows w176Rows := by
  rw [w176, eval_append]
  exact eval_mul ρ eval_w175 eval_w3 (decoded_product product_w176)
private theorem eval_w177 : ρ (evalWord nativeAlphabet w177) = decodeRows w177Rows := by
  rw [w177, eval_append]
  exact eval_mul ρ eval_w176 eval_w65 (decoded_product product_w177)
private theorem eval_w178 : ρ (evalWord nativeAlphabet w178) = decodeRows w178Rows := by
  rw [w178, eval_append]
  exact eval_mul ρ eval_w40 eval_w20 (decoded_product product_w178)
private theorem eval_w179 : ρ (evalWord nativeAlphabet w179) = decodeRows w179Rows := by
  rw [w179, eval_append]
  exact eval_mul ρ eval_w178 eval_w15 (decoded_product product_w179)
private theorem eval_w180 : ρ (evalWord nativeAlphabet w180) = decodeRows w180Rows := by
  rw [w180, eval_append]
  exact eval_mul ρ eval_w179 eval_w62 (decoded_product product_w180)
private theorem eval_w181 : ρ (evalWord nativeAlphabet w181) = decodeRows w181Rows := by
  rw [w181, eval_append]
  exact eval_mul ρ eval_w180 eval_w8 (decoded_product product_w181)
private theorem eval_w182 : ρ (evalWord nativeAlphabet w182) = decodeRows w182Rows := by
  rw [w182, eval_append]
  exact eval_mul ρ eval_w181 eval_w17 (decoded_product product_w182)
private theorem eval_w183 : ρ (evalWord nativeAlphabet w183) = decodeRows w183Rows := by
  rw [w183, eval_append]
  exact eval_mul ρ eval_w182 eval_w34 (decoded_product product_w183)
private theorem eval_w184 : ρ (evalWord nativeAlphabet w184) = decodeRows w184Rows := by
  rw [w184, eval_append]
  exact eval_mul ρ eval_w183 eval_w12 (decoded_product product_w184)
private theorem eval_w185 : ρ (evalWord nativeAlphabet w185) = decodeRows w185Rows := by
  rw [w185, eval_append]
  exact eval_mul ρ eval_w184 eval_w23 (decoded_product product_w185)
private theorem eval_w186 : ρ (evalWord nativeAlphabet w186) = decodeRows w186Rows := by
  rw [w186, eval_append]
  exact eval_mul ρ eval_w185 eval_w12 (decoded_product product_w186)
private theorem eval_w187 : ρ (evalWord nativeAlphabet w187) = decodeRows w187Rows := by
  rw [w187, eval_append]
  exact eval_mul ρ eval_w186 eval_w8 (decoded_product product_w187)
private theorem eval_w188 : ρ (evalWord nativeAlphabet w188) = decodeRows w188Rows := by
  rw [w188, eval_append]
  exact eval_mul ρ eval_w187 eval_w47 (decoded_product product_w188)
private theorem eval_w189 : ρ (evalWord nativeAlphabet w189) = decodeRows w189Rows := by
  rw [w189, eval_append]
  exact eval_mul ρ eval_w188 eval_w17 (decoded_product product_w189)
private theorem eval_w190 : ρ (evalWord nativeAlphabet w190) = decodeRows w190Rows := by
  rw [w190, eval_append]
  exact eval_mul ρ eval_w189 eval_w58 (decoded_product product_w190)
private theorem eval_w191 : ρ (evalWord nativeAlphabet w191) = decodeRows w191Rows := by
  rw [w191, eval_append]
  exact eval_mul ρ eval_w190 eval_w0 (decoded_product product_w191)
private theorem eval_w192 : ρ (evalWord nativeAlphabet w192) = decodeRows w192Rows := by
  rw [w192, eval_append]
  exact eval_mul ρ eval_w191 eval_w60 (decoded_product product_w192)
private theorem eval_w193 : ρ (evalWord nativeAlphabet w193) = decodeRows w193Rows := by
  rw [w193, eval_append]
  exact eval_mul ρ eval_w192 eval_w17 (decoded_product product_w193)
private theorem eval_w194 : ρ (evalWord nativeAlphabet w194) = decodeRows w194Rows := by
  rw [w194, eval_append]
  exact eval_mul ρ eval_w193 eval_w42 (decoded_product product_w194)
private theorem eval_w195 : ρ (evalWord nativeAlphabet w195) = decodeRows w195Rows := by
  rw [w195, eval_append]
  exact eval_mul ρ eval_w194 eval_w11 (decoded_product product_w195)
private theorem eval_w196 : ρ (evalWord nativeAlphabet w196) = decodeRows w196Rows := by
  rw [w196, eval_append]
  exact eval_mul ρ eval_w195 eval_w13 (decoded_product product_w196)
private theorem eval_w197 : ρ (evalWord nativeAlphabet w197) = decodeRows w197Rows := by
  rw [w197, eval_append]
  exact eval_mul ρ eval_w196 eval_w33 (decoded_product product_w197)
private theorem eval_w198 : ρ (evalWord nativeAlphabet w198) = decodeRows w198Rows := by
  rw [w198, eval_append]
  exact eval_mul ρ eval_w197 eval_w14 (decoded_product product_w198)
private theorem eval_w199 : ρ (evalWord nativeAlphabet w199) = decodeRows w199Rows := by
  rw [w199, eval_append]
  exact eval_mul ρ eval_w198 eval_w43 (decoded_product product_w199)
private theorem eval_w200 : ρ (evalWord nativeAlphabet w200) = decodeRows w200Rows := by
  rw [w200, eval_append]
  exact eval_mul ρ eval_w199 eval_w0 (decoded_product product_w200)
private theorem eval_w201 : ρ (evalWord nativeAlphabet w201) = decodeRows w201Rows := by
  rw [w201, eval_append]
  exact eval_mul ρ eval_w200 eval_w65 (decoded_product product_w201)

private theorem eval_basis (i : Fin 11) :
    ρ (nativeMask (2^i.val)) = decodeRows (basisRows i) := by
  rw [show nativeMask (2^i.val) = basis matrixA_mul_self matrixB_pow_four i from
    maskValue_basis matrixA_mul_self matrixB_pow_four i]
  exact representation_basis _ _ i
private theorem eval_k192 : ρ (nativeMask 192) = decodeRows k192Rows := by
  rw [show nativeMask 192 = nativeMask 64 * nativeMask 128 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 64 128)]
  exact eval_mul ρ (eval_basis 6) (eval_basis 7) (decoded_product product_k192)
private theorem eval_k448 : ρ (nativeMask 448) = decodeRows k448Rows := by
  rw [show nativeMask 448 = nativeMask 192 * nativeMask 256 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 192 256)]
  exact eval_mul ρ eval_k192 (eval_basis 8) (decoded_product product_k448)
private theorem eval_k1472 : ρ (nativeMask 1472) = decodeRows k1472Rows := by
  rw [show nativeMask 1472 = nativeMask 448 * nativeMask 1024 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 448 1024)]
  exact eval_mul ρ eval_k448 (eval_basis 10) (decoded_product product_k1472)
private theorem eval_k544 : ρ (nativeMask 544) = decodeRows k544Rows := by
  rw [show nativeMask 544 = nativeMask 32 * nativeMask 512 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 32 512)]
  exact eval_mul ρ (eval_basis 5) (eval_basis 9) (decoded_product product_k544)
private theorem eval_k36 : ρ (nativeMask 36) = decodeRows k36Rows := by
  rw [show nativeMask 36 = nativeMask 4 * nativeMask 32 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 4 32)]
  exact eval_mul ρ (eval_basis 2) (eval_basis 5) (decoded_product product_k36)
private theorem eval_k100 : ρ (nativeMask 100) = decodeRows k100Rows := by
  rw [show nativeMask 100 = nativeMask 36 * nativeMask 64 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 36 64)]
  exact eval_mul ρ eval_k36 (eval_basis 6) (decoded_product product_k100)
private theorem eval_k228 : ρ (nativeMask 228) = decodeRows k228Rows := by
  rw [show nativeMask 228 = nativeMask 100 * nativeMask 128 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 100 128)]
  exact eval_mul ρ eval_k100 (eval_basis 7) (decoded_product product_k228)
private theorem eval_k740 : ρ (nativeMask 740) = decodeRows k740Rows := by
  rw [show nativeMask 740 = nativeMask 228 * nativeMask 512 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 228 512)]
  exact eval_mul ρ eval_k228 (eval_basis 9) (decoded_product product_k740)
private theorem eval_k1764 : ρ (nativeMask 1764) = decodeRows k1764Rows := by
  rw [show nativeMask 1764 = nativeMask 740 * nativeMask 1024 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 740 1024)]
  exact eval_mul ρ eval_k740 (eval_basis 10) (decoded_product product_k1764)
private theorem eval_k288 : ρ (nativeMask 288) = decodeRows k288Rows := by
  rw [show nativeMask 288 = nativeMask 32 * nativeMask 256 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 32 256)]
  exact eval_mul ρ (eval_basis 5) (eval_basis 8) (decoded_product product_k288)
private theorem eval_k800 : ρ (nativeMask 800) = decodeRows k800Rows := by
  rw [show nativeMask 800 = nativeMask 288 * nativeMask 512 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 288 512)]
  exact eval_mul ρ eval_k288 (eval_basis 9) (decoded_product product_k800)
private theorem eval_k1824 : ρ (nativeMask 1824) = decodeRows k1824Rows := by
  rw [show nativeMask 1824 = nativeMask 800 * nativeMask 1024 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 800 1024)]
  exact eval_mul ρ eval_k800 (eval_basis 10) (decoded_product product_k1824)
private theorem eval_k160 : ρ (nativeMask 160) = decodeRows k160Rows := by
  rw [show nativeMask 160 = nativeMask 32 * nativeMask 128 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 32 128)]
  exact eval_mul ρ (eval_basis 5) (eval_basis 7) (decoded_product product_k160)
private theorem eval_k672 : ρ (nativeMask 672) = decodeRows k672Rows := by
  rw [show nativeMask 672 = nativeMask 160 * nativeMask 512 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 160 512)]
  exact eval_mul ρ eval_k160 (eval_basis 9) (decoded_product product_k672)
private theorem eval_k576 : ρ (nativeMask 576) = decodeRows k576Rows := by
  rw [show nativeMask 576 = nativeMask 64 * nativeMask 512 from
    congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four 64 512)]
  exact eval_mul ρ (eval_basis 6) (eval_basis 9) (decoded_product product_k576)

theorem representation_correctedLift (i : Fin 6) :
    ρ (correctedLift i) = decodeRows (correctedRows i) := by
  unfold correctedLift permutationLift
  rw [← finalWord_eq]
  fin_cases i
  · exact eval_mul ρ eval_k1472 eval_w88 (decoded_product product_l0)
  · exact eval_mul ρ eval_k544 eval_w105 (decoded_product product_l1)
  · exact eval_mul ρ eval_k1764 eval_w125 (decoded_product product_l2)
  · exact eval_mul ρ eval_k1824 eval_w157 (decoded_product product_l3)
  · exact eval_mul ρ eval_k672 eval_w177 (decoded_product product_l4)
  · exact eval_mul ρ eval_k576 eval_w201 (decoded_product product_l5)
end Janko4.LocalStructure.ElementaryEightGeometry
