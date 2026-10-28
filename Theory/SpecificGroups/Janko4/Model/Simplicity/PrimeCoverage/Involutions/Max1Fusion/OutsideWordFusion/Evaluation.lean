module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideSetup
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion.Products0

/-!
# Evaluation of conjugated fusion targets

We evaluate positive words and their inverses in the actual `Model` group.
The inverse rows are justified by a checked right-inverse equation; hence
no invertibility or conjugacy claim in an ambient general linear group is used.
-/

public section
namespace Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
open Janko4.Cardinality Janko4.Cardinality.KernelCount
open Janko4.Cardinality.KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
open Part0
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

theorem decode_target :
    decodeRows d5Rows = toMatrix (word (a hA) (b hB) "ababb" ^ 5) := by
  have hc : decodeRows cRows = matrixA * matrixB := by
    rw [← product_a_b, decode_packedMul]
    rfl
  have hc2 : decodeRows c2Rows = (matrixA * matrixB) ^ 2 := by
    rw [← product_c_c, decode_packedMul, hc, pow_two]
  have hd : decodeRows dRows = matrixA * matrixB * matrixA * matrixB * matrixB := by
    rw [← product_c2_b, decode_packedMul, hc2, pow_two]
    simp only [matrixB, mul_assoc]
  have hd2 : decodeRows d2Rows = (decodeRows dRows) ^ 2 := by
    rw [← product_d_d, decode_packedMul, pow_two]
  have hd4 : decodeRows d4Rows = (decodeRows dRows) ^ 4 := by
    rw [← product_d2_d2, decode_packedMul, hd2, ← pow_add]
  rw [← product_d4_d, decode_packedMul, hd4, ← pow_succ, hd]
  simp [word, mul_assoc]

theorem decode_xy7 :
    decodeRows xy7Rows = representation hA hB ((localX hA hB * localY hA hB) ^ 7) := by
  have h2 : decodeRows xy2Rows = decodeRows xyRows ^ 2 := by
    rw [← decoded_product product_xy2, pow_two]
  have h4 : decodeRows xy4Rows = decodeRows xyRows ^ 4 := by
    rw [← decoded_product product_xy4, h2, ← pow_add]
  have h6 : decodeRows xy6Rows = decodeRows xyRows ^ 6 := by
    rw [← decoded_product product_00, h4, h2, ← pow_add]
  rw [← decoded_product product_01, h6, ← pow_succ]
  rw [map_pow, map_mul, representation_x, representation_y, decoded_product product_xy]

theorem eval_w0 : toMatrix (word (a hA) (b hB) "b") = decodeRows bRows := by
  have ha : toMatrix (a hA) = decodeRows aRows := rfl
  have hb : toMatrix (b hB) = decodeRows bRows := rfl
  simpa [word, mul_assoc] using hb

theorem eval_w0_inv : toMatrix (word (a hA) (b hB) "b")⁻¹ = decodeRows wi0Rows :=
  eval_inv toMatrix (eval_w0 hA hB)
    (by rw [decoded_product product_02, decode_packedOne])

theorem eval_w1 : toMatrix (word (a hA) (b hB) "bb") = decodeRows w1_1Rows := by
  have ha : toMatrix (a hA) = decodeRows aRows := rfl
  have hb : toMatrix (b hB) = decodeRows bRows := rfl
  have hw1 := eval_mul toMatrix hb hb (decoded_product product_03)
  simpa [word, mul_assoc] using hw1

theorem eval_w1_inv : toMatrix (word (a hA) (b hB) "bb")⁻¹ = decodeRows wi1Rows :=
  eval_inv toMatrix (eval_w1 hA hB)
    (by rw [decoded_product product_04, decode_packedOne])

theorem eval_w2 : toMatrix (word (a hA) (b hB) "bbabbbbbba") = decodeRows w2_9Rows := by
  have ha : toMatrix (a hA) = decodeRows aRows := rfl
  have hb : toMatrix (b hB) = decodeRows bRows := rfl
  have hw1 := eval_mul toMatrix hb hb (decoded_product product_05)
  have hw2 := eval_mul toMatrix hw1 ha (decoded_product product_06)
  have hw3 := eval_mul toMatrix hw2 hb (decoded_product product_07)
  have hw4 := eval_mul toMatrix hw3 hb (decoded_product product_08)
  have hw5 := eval_mul toMatrix hw4 hb (decoded_product product_09)
  have hw6 := eval_mul toMatrix hw5 hb (decoded_product product_10)
  have hw7 := eval_mul toMatrix hw6 hb (decoded_product product_11)
  have hw8 := eval_mul toMatrix hw7 hb (decoded_product product_12)
  have hw9 := eval_mul toMatrix hw8 ha (decoded_product product_13)
  simpa [word, mul_assoc] using hw9

theorem eval_w2_inv : toMatrix (word (a hA) (b hB) "bbabbbbbba")⁻¹ = decodeRows wi2Rows :=
  eval_inv toMatrix (eval_w2 hA hB)
    (by rw [decoded_product product_14, decode_packedOne])

theorem eval_conj0Rows :
    toMatrix (word (a hA) (b hB) "b" * (word (a hA) (b hB) "ababb" ^ 5) * (word (a hA) (b hB) "b")⁻¹) = decodeRows conj0Rows := by
  have ht : toMatrix (word (a hA) (b hB) "ababb" ^ 5) = decodeRows d5Rows := (decode_target hA hB).symm
  exact eval_mul toMatrix
    (eval_mul toMatrix (eval_w0 hA hB) ht (decoded_product product_15))
    (eval_w0_inv hA hB) (decoded_product product_16)

theorem eval_conj1Rows :
    toMatrix (word (a hA) (b hB) "bb" * (word (a hA) (b hB) "ababb" ^ 5) * (word (a hA) (b hB) "bb")⁻¹) = decodeRows conj1Rows := by
  have ht : toMatrix (word (a hA) (b hB) "ababb" ^ 5) = decodeRows d5Rows := (decode_target hA hB).symm
  exact eval_mul toMatrix
    (eval_mul toMatrix (eval_w1 hA hB) ht (decoded_product product_17))
    (eval_w1_inv hA hB) (decoded_product product_18)

theorem eval_conj2Rows :
    toMatrix (word (a hA) (b hB) "bbabbbbbba" * (word (a hA) (b hB) "ababb" ^ 5) * (word (a hA) (b hB) "bbabbbbbba")⁻¹) = decodeRows conj2Rows := by
  have ht : toMatrix (word (a hA) (b hB) "ababb" ^ 5) = decodeRows d5Rows := (decode_target hA hB).symm
  exact eval_mul toMatrix
    (eval_mul toMatrix (eval_w2 hA hB) ht (decoded_product product_19))
    (eval_w2_inv hA hB) (decoded_product product_20)

theorem eval_conj3Rows :
    toMatrix (word (a hA) (b hB) "b" * (a hA) * (word (a hA) (b hB) "b")⁻¹) = decodeRows conj3Rows := by
  have ht : toMatrix (a hA) = decodeRows aRows := rfl
  exact eval_mul toMatrix
    (eval_mul toMatrix (eval_w0 hA hB) ht (decoded_product product_21))
    (eval_w0_inv hA hB) (decoded_product product_22)

end Janko4.Simplicity.Max1Fusion.OutsideWordCertificates
