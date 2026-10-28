module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Elements
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Products.Part0
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Products.Part1
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Products.Part2
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Products.Part3

/-!
# Evaluation of the actual max4 words

Each register assignment and each signed seed letter is transported through the
faithful matrix homomorphism. The certificates prove the candidate rows are the
matrices of actual words inside max4. Conjugation uses the convention w⁻¹ z w.
The elementary structure and relative normality are proved in Tables and the
owning NormalEight module.
-/

public section

namespace Janko4.LocalStructure.SymmetricLinear.NormalEight
open Janko4.GeneratorCertificates

private lemma decoded_product {a b c : Vector ℕ 112} (h : packedMul a b = c) :
    decodeRows a * decodeRows b = decodeRows c := by
  rw [← decode_packedMul, h]

private lemma eval_mul {G M : Type*} [Group G] [Monoid M] (f : G →* M)
    {a b : G} {A B C : M} (ha : f a = A) (hb : f b = B) (h : A * B = C) :
    f (a * b) = C := by rw [map_mul, ha, hb, h]

private lemma eval_inv {G M : Type*} [Group G] [Monoid M] (f : G →* M)
    {a : G} {A B : M} (ha : f a = A) (h : A * B = 1) : f a⁻¹ = B := by
  calc
    f a⁻¹ = f a⁻¹ * (A * B) := by rw [h, mul_one]
    _ = B := by rw [← ha, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private lemma eval_conj {G M : Type*} [Group G] [Monoid M] (f : G →* M)
    {a g : G} {A B C : M} (ha : f a = A) (hg : f g = B)
    (h : A * B = B * C) : f (g⁻¹ * a * g) = C := by
  calc
    f (g⁻¹ * a * g) = f g⁻¹ * (A * B) := by rw [map_mul, map_mul, ha, hg, mul_assoc]
    _ = f g⁻¹ * (B * C) := by rw [h]
    _ = C := by rw [← hg, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem decode_a : decodeRows aRows = toMatrix a := rfl

private theorem decode_b : decodeRows bRows = toMatrix b := rfl

private def stage01 : Model := a * b

private theorem decode_stage01 : decodeRows product_stage01Rows = toMatrix stage01 := by
  change _ = toMatrix (a * b)
  rw [map_mul, ← decode_a, ← decode_b, ← decode_packedMul, product_stage01]

private theorem decode_stage02Power1 : decodeRows product_stage01Rows = decodeRows product_stage01Rows ^ 1 := by simp

private theorem decode_stage02Power2 : decodeRows stage02Power2Rows = decodeRows product_stage01Rows ^ 2 := by
  rw [← stage02Power2, decode_packedMul, pow_two]

private theorem decode_stage02Power3 : decodeRows stage02Power3Rows = decodeRows product_stage01Rows ^ 3 := by
  rw [← stage02Power3, decode_packedMul, decode_stage02Power2, ← pow_succ]

private def stage02 : Model := stage01 ^ 3

private theorem decode_stage02 : decodeRows stage02Power3Rows = toMatrix stage02 := by
  change _ = toMatrix (stage01 ^ 3)
  rw [map_pow, ← decode_stage01]
  exact decode_stage02Power3

private def stage03 : Model := stage02 * b

private theorem decode_stage03 : decodeRows product_stage03Rows = toMatrix stage03 := by
  change _ = toMatrix (stage02 * b)
  rw [map_mul, ← decode_stage02, ← decode_b, ← decode_packedMul, product_stage03]

private def stage04 : Model := b * a

private theorem decode_stage04 : decodeRows product_stage04Rows = toMatrix stage04 := by
  change _ = toMatrix (b * a)
  rw [map_mul, ← decode_b, ← decode_a, ← decode_packedMul, product_stage04]

private def stage05 : Model := stage03 * b

private theorem decode_stage05 : decodeRows product_stage05Rows = toMatrix stage05 := by
  change _ = toMatrix (stage03 * b)
  rw [map_mul, ← decode_stage03, ← decode_b, ← decode_packedMul, product_stage05]

private theorem decode_stage06Power1 : decodeRows product_stage05Rows = decodeRows product_stage05Rows ^ 1 := by simp

private theorem decode_stage06Power2 : decodeRows stage06Power2Rows = decodeRows product_stage05Rows ^ 2 := by
  rw [← stage06Power2, decode_packedMul, pow_two]

private theorem decode_stage06Power3 : decodeRows stage06Power3Rows = decodeRows product_stage05Rows ^ 3 := by
  rw [← stage06Power3, decode_packedMul, decode_stage06Power2, ← pow_succ]

private def stage06 : Model := stage05 ^ 3

private theorem decode_stage06 : decodeRows stage06Power3Rows = toMatrix stage06 := by
  change _ = toMatrix (stage05 ^ 3)
  rw [map_pow, ← decode_stage05]
  exact decode_stage06Power3

private theorem decode_stage07Power1 : decodeRows product_stage04Rows = decodeRows product_stage04Rows ^ 1 := by simp

private theorem decode_stage07Power2 : decodeRows stage07Power2Rows = decodeRows product_stage04Rows ^ 2 := by
  rw [← stage07Power2, decode_packedMul, pow_two]

private theorem decode_stage07Power4 : decodeRows stage07Power4Rows = decodeRows product_stage04Rows ^ 4 := by
  rw [← stage07Power4, decode_packedMul, decode_stage07Power2, ← pow_add]

private theorem decode_stage07Power5 : decodeRows stage07Power5Rows = decodeRows product_stage04Rows ^ 5 := by
  rw [← stage07Power5, decode_packedMul, decode_stage07Power4, ← pow_succ]

private theorem decode_stage07Power10 : decodeRows stage07Power10Rows = decodeRows product_stage04Rows ^ 10 := by
  rw [← stage07Power10, decode_packedMul, decode_stage07Power5, ← pow_add]

private theorem decode_stage07Power11 : decodeRows stage07Power11Rows = decodeRows product_stage04Rows ^ 11 := by
  rw [← stage07Power11, decode_packedMul, decode_stage07Power10, ← pow_succ]

private theorem decode_stage07Power22 : decodeRows stage07Power22Rows = decodeRows product_stage04Rows ^ 22 := by
  rw [← stage07Power22, decode_packedMul, decode_stage07Power11, ← pow_add]

private def stage07 : Model := stage04 ^ 22

private theorem decode_stage07 : decodeRows stage07Power22Rows = toMatrix stage07 := by
  change _ = toMatrix (stage04 ^ 22)
  rw [map_pow, ← decode_stage04]
  exact decode_stage07Power22

private theorem decode_stage08Power6 : decodeRows stage08Power6Rows = decodeRows product_stage01Rows ^ 6 := by
  rw [← stage08Power6, decode_packedMul, decode_stage02Power3, ← pow_add]

private theorem decode_stage08Power12 : decodeRows stage08Power12Rows = decodeRows product_stage01Rows ^ 12 := by
  rw [← stage08Power12, decode_packedMul, decode_stage08Power6, ← pow_add]

private theorem decode_stage08Power13 : decodeRows stage08Power13Rows = decodeRows product_stage01Rows ^ 13 := by
  rw [← stage08Power13, decode_packedMul, decode_stage08Power12, ← pow_succ]

private def stage08 : Model := stage01 ^ 13

private theorem decode_stage08 : decodeRows stage08Power13Rows = toMatrix stage08 := by
  change _ = toMatrix (stage01 ^ 13)
  rw [map_pow, ← decode_stage01]
  exact decode_stage08Power13

private def stage09 : Model := stage07 * stage08

private theorem decode_stage09 : decodeRows product_stage09Rows = toMatrix stage09 := by
  change _ = toMatrix (stage07 * stage08)
  rw [map_mul, ← decode_stage07, ← decode_stage08, ← decode_packedMul, product_stage09]

private def stage10 : Model := stage04 * stage04

private theorem decode_stage10 : decodeRows product_stage10Rows = toMatrix stage10 := by
  change _ = toMatrix (stage04 * stage04)
  rw [map_mul, ← decode_stage04, ← decode_packedMul, product_stage10]

private def stage11 : Model := stage09⁻¹

private theorem decode_stage11 : decodeRows stage11Rows = toMatrix stage11 := by
  change _ = toMatrix (stage09⁻¹)
  apply left_inv_eq_right_inv (a := toMatrix stage09)
  · rw [← decode_stage09, ← decode_packedMul, product_stage11, decode_packedOne]
  · rw [← map_mul, mul_inv_cancel, map_one]

private def stage12 : Model := stage11 * stage06

private theorem decode_stage12 : decodeRows product_stage12Rows = toMatrix stage12 := by
  change _ = toMatrix (stage11 * stage06)
  rw [map_mul, ← decode_stage11, ← decode_stage06, ← decode_packedMul, product_stage12]

private def stage13 : Model := stage06 * stage06

private theorem decode_stage13 : decodeRows product_stage13Rows = toMatrix stage13 := by
  change _ = toMatrix (stage06 * stage06)
  rw [map_mul, ← decode_stage06, ← decode_packedMul, product_stage13]

private def stage14 : Model := stage12 * stage09

private theorem decode_stage14 : decodeRows product_stage14Rows = toMatrix stage14 := by
  change _ = toMatrix (stage12 * stage09)
  rw [map_mul, ← decode_stage12, ← decode_stage09, ← decode_packedMul, product_stage14]

private def stage15 : Model := stage10⁻¹

private theorem decode_stage15 : decodeRows stage15Rows = toMatrix stage15 := by
  change _ = toMatrix (stage10⁻¹)
  apply left_inv_eq_right_inv (a := toMatrix stage10)
  · rw [← decode_stage10, ← decode_packedMul, product_stage15, decode_packedOne]
  · rw [← map_mul, mul_inv_cancel, map_one]

private def stage16 : Model := stage15 * stage13

private theorem decode_stage16 : decodeRows product_stage16Rows = toMatrix stage16 := by
  change _ = toMatrix (stage15 * stage13)
  rw [map_mul, ← decode_stage15, ← decode_stage13, ← decode_packedMul, product_stage16]

private def stage17 : Model := stage16 * stage10

private theorem decode_stage17 : decodeRows product_stage17Rows = toMatrix stage17 := by
  change _ = toMatrix (stage16 * stage10)
  rw [map_mul, ← decode_stage16, ← decode_stage10, ← decode_packedMul, product_stage17]

theorem matrix_x : matrix x = decodeRows xRows := decode_stage17.symm

theorem matrix_y : matrix y = decodeRows yRows := decode_stage14.symm

private theorem matrix_x_inverse : matrix x⁻¹ = decodeRows xInverseRows :=
  eval_inv matrix matrix_x (by rw [← decode_packedMul, x_inverse, decode_packedOne])

private theorem matrix_y_inverse : matrix y⁻¹ = decodeRows yInverseRows :=
  eval_inv matrix matrix_y (by rw [← decode_packedMul, y_inverse, decode_packedOne])

private def wordValue1 : max4Subgroup := x⁻¹ * y

private theorem matrix_word1 : matrix wordValue1 = decodeRows word1Rows :=
  eval_mul matrix matrix_x_inverse matrix_y (decoded_product word1)

private def wordValue2 : max4Subgroup := wordValue1 * x

private theorem matrix_word2 : matrix wordValue2 = decodeRows word2Rows :=
  eval_mul matrix matrix_word1 matrix_x (decoded_product word2)

private def wordValue3 : max4Subgroup := wordValue2 * x

private theorem matrix_word3 : matrix wordValue3 = decodeRows word3Rows :=
  eval_mul matrix matrix_word2 matrix_x (decoded_product word3)

private def wordValue4 : max4Subgroup := wordValue3 * x

private theorem matrix_word4 : matrix wordValue4 = decodeRows word4Rows :=
  eval_mul matrix matrix_word3 matrix_x (decoded_product word4)

private def wordValue5 : max4Subgroup := wordValue4 * y⁻¹

private theorem matrix_word5 : matrix wordValue5 = decodeRows word5Rows :=
  eval_mul matrix matrix_word4 matrix_y_inverse (decoded_product word5)

private def wordValue6 : max4Subgroup := wordValue5 * x⁻¹

private theorem matrix_word6 : matrix wordValue6 = decodeRows word6Rows :=
  eval_mul matrix matrix_word5 matrix_x_inverse (decoded_product word6)

private def wordValue7 : max4Subgroup := wordValue6 * y⁻¹

private theorem matrix_word7 : matrix wordValue7 = decodeRows word7Rows :=
  eval_mul matrix matrix_word6 matrix_y_inverse (decoded_product word7)

private def wordValue8 : max4Subgroup := wordValue7 * x⁻¹

private theorem matrix_word8 : matrix wordValue8 = decodeRows word8Rows :=
  eval_mul matrix matrix_word7 matrix_x_inverse (decoded_product word8)

private def wordValue9 : max4Subgroup := wordValue8 * x⁻¹

private theorem matrix_word9 : matrix wordValue9 = decodeRows word9Rows :=
  eval_mul matrix matrix_word8 matrix_x_inverse (decoded_product word9)

private theorem decode_seedPower1 : decodeRows word9Rows = decodeRows word9Rows ^ 1 := by simp

private theorem decode_seedPower2 : decodeRows seedPower2Rows = decodeRows word9Rows ^ 2 := by
  rw [← seedPower2, decode_packedMul, pow_two]

private theorem decode_seedPower3 : decodeRows seedPower3Rows = decodeRows word9Rows ^ 3 := by
  rw [← seedPower3, decode_packedMul, decode_seedPower2, ← pow_succ]

private theorem decode_seedPower6 : decodeRows seedPower6Rows = decodeRows word9Rows ^ 6 := by
  rw [← seedPower6, decode_packedMul, decode_seedPower3, ← pow_add]

theorem matrix_seed : matrix seed = decodeRows seedPower6Rows := by
  change matrix (wordValue9 ^ 6) = _
  rw [map_pow, matrix_word9]
  exact decode_seedPower6.symm

theorem matrix_e2 : matrix e2 = decodeRows e2Rows :=
  eval_conj matrix matrix_seed matrix_y (by
    rw [← decode_packedMul, orbit2_left, ← orbit2_right, decode_packedMul])

theorem matrix_e3 : matrix e3 = decodeRows e3Rows :=
  eval_conj matrix matrix_e2 matrix_x (by
    rw [← decode_packedMul, orbit3_left, ← orbit3_right, decode_packedMul])

theorem matrix_e4 : matrix e4 = decodeRows e4Rows :=
  eval_conj matrix matrix_e2 matrix_y (by
    rw [← decode_packedMul, orbit4_left, ← orbit4_right, decode_packedMul])

theorem matrix_e5 : matrix e5 = decodeRows e5Rows :=
  eval_conj matrix matrix_e4 matrix_x (by
    rw [← decode_packedMul, orbit5_left, ← orbit5_right, decode_packedMul])

theorem matrix_e6 : matrix e6 = decodeRows e6Rows :=
  eval_conj matrix matrix_e4 matrix_y (by
    rw [← decode_packedMul, orbit6_left, ← orbit6_right, decode_packedMul])

theorem matrix_e7 : matrix e7 = decodeRows e7Rows :=
  eval_conj matrix matrix_e5 matrix_y (by
    rw [← decode_packedMul, orbit7_left, ← orbit7_right, decode_packedMul])

theorem matrix_element (i : Fin 8) : matrix (element i) = decodeRows (elementRows i) := by
  fin_cases i
  · exact (map_one matrix).trans decode_packedOne.symm
  · exact matrix_seed
  · exact matrix_e2
  · exact matrix_e3
  · exact matrix_e4
  · exact matrix_e5
  · exact matrix_e6
  · exact matrix_e7

end Janko4.LocalStructure.SymmetricLinear.NormalEight
