module

public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.Second.Words
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.Second.Products12

/-!
# Matrix witnesses for the second J₄ involution triple

Untrusted row data for words in `r`, `a*r*a⁻¹`, `b*r*b⁻¹`, where
`r = (a*b*a*b*b)^5`. The product certificates check every multiplication
in the kernel. The invertible matrix T intertwines the original generators
with two such words; no ATLAS generation test is trusted by the proof.

Source matrices: ATLAS J4G1-f2r112B0, as attributed in `Model.Data`.
The word search used the ATLAS J4G1-find1 recipe (Wilson–Nickerson–Bray);
see `source/README.md` for the reproducible witness and proof method.
-/

@[expose] public section
namespace Janko4.ThreeConjugates.SecondCertificate
open GeneratorCertificates

private theorem mul_certificate {g h : Model} {rs ss ts : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hh : toMatrix h = decodeRows ss)
    (hc : packedMul rs ss = ts) : toMatrix (g * h) = decodeRows ts := by
  rw [map_mul, hg, hh, ← decode_packedMul, hc]

private theorem inv_certificate {g : Model} {rs ss : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hc : packedMul rs ss = packedOne) :
    toMatrix g⁻¹ = decodeRows ss := by
  have h : toMatrix g * decodeRows ss = 1 := by
    rw [hg, ← decode_packedMul, hc, decode_packedOne]
  calc
    toMatrix g⁻¹ = toMatrix g⁻¹ * 1 := (mul_one _).symm
    _ = toMatrix g⁻¹ * (toMatrix g * decodeRows ss) := by rw [h]
    _ = decodeRows ss := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

private theorem eval_a : toMatrix a = decodeRows aRows := rfl
private theorem eval_b : toMatrix b = decodeRows bRows := rfl

theorem eval_r : toMatrix r = decodeRows d5Rows := by
  have hc : decodeRows cRows = matrixA * matrixB := by
    rw [← product_a_b, decode_packedMul]
    rfl
  have hc2 : decodeRows c2Rows = (matrixA * matrixB) ^ 2 := by
    rw [← product_c_c, decode_packedMul, hc, pow_two]
  have hd : decodeRows dRows = matrixA * matrixB * matrixA * matrixB * matrixB := by
    rw [← product_c2_b, decode_packedMul, hc2, pow_two]
    simp only [matrixB, mul_assoc]
  have hd2 : decodeRows d2Rows = (matrixA * matrixB * matrixA * matrixB * matrixB) ^ 2 := by
    rw [← product_d_d, decode_packedMul, hd, pow_two]
  have hd4 : decodeRows d4Rows = (matrixA * matrixB * matrixA * matrixB * matrixB) ^ 4 := by
    rw [← product_d2_d2, decode_packedMul, hd2, ← pow_add]
  rw [r, map_pow, map_mul, map_mul, map_mul, map_mul, toMatrix_a, toMatrix_b,
    ← product_d4_d, decode_packedMul, hd4, hd, ← pow_succ]


theorem eval_ai : toMatrix ai = decodeRows aiRows :=
  inv_certificate eval_a product_ai

theorem eval_bi : toMatrix bi = decodeRows biRows :=
  inv_certificate eval_b product_bi

theorem eval_ar : toMatrix ar = decodeRows arRows :=
  mul_certificate eval_a eval_r product_ar

theorem eval_x : toMatrix x = decodeRows xRows :=
  mul_certificate eval_ar eval_ai product_x

theorem eval_br : toMatrix br = decodeRows brRows :=
  mul_certificate eval_b eval_r product_br

theorem eval_y : toMatrix y = decodeRows yRows :=
  mul_certificate eval_br eval_bi product_y

theorem eval_u1 : toMatrix u1 = decodeRows u1Rows :=
  mul_certificate eval_r eval_y product_u1

theorem eval_u2 : toMatrix u2 = decodeRows u2Rows :=
  mul_certificate eval_u1 eval_r product_u2

theorem eval_u3 : toMatrix u3 = decodeRows u3Rows :=
  mul_certificate eval_u2 eval_x product_u3

theorem eval_u4 : toMatrix u4 = decodeRows u4Rows :=
  mul_certificate eval_u3 eval_r product_u4

theorem eval_u5 : toMatrix u5 = decodeRows u5Rows :=
  mul_certificate eval_u4 eval_x product_u5

theorem eval_u6 : toMatrix u6 = decodeRows u6Rows :=
  mul_certificate eval_u5 eval_r product_u6

theorem eval_u7 : toMatrix u7 = decodeRows u7Rows :=
  mul_certificate eval_u6 eval_x product_u7

theorem eval_u8 : toMatrix u8 = decodeRows u8Rows :=
  mul_certificate eval_u7 eval_y product_u8

theorem eval_u9 : toMatrix u9 = decodeRows u9Rows :=
  mul_certificate eval_u8 eval_r product_u9

theorem eval_u10 : toMatrix u10 = decodeRows u10Rows :=
  mul_certificate eval_u9 eval_y product_u10

theorem eval_u11 : toMatrix u11 = decodeRows u11Rows :=
  mul_certificate eval_u10 eval_r product_u11

theorem eval_u12 : toMatrix u12 = decodeRows u12Rows :=
  mul_certificate eval_u11 eval_y product_u12

theorem eval_u13 : toMatrix u13 = decodeRows u13Rows :=
  mul_certificate eval_u12 eval_x product_u13

theorem eval_u14 : toMatrix u14 = decodeRows u14Rows :=
  mul_certificate eval_u13 eval_y product_u14

theorem eval_u15 : toMatrix u15 = decodeRows u15Rows :=
  mul_certificate eval_u14 eval_x product_u15

theorem eval_v1 : toMatrix v1 = decodeRows v1Rows :=
  mul_certificate eval_x eval_y product_v1

theorem eval_v2 : toMatrix v2 = decodeRows v2Rows :=
  mul_certificate eval_v1 eval_r product_v2

theorem eval_v3 : toMatrix v3 = decodeRows v3Rows :=
  mul_certificate eval_v2 eval_y product_v3

theorem eval_v4 : toMatrix v4 = decodeRows v4Rows :=
  mul_certificate eval_v3 eval_x product_v4

theorem eval_v5 : toMatrix v5 = decodeRows v5Rows :=
  mul_certificate eval_v4 eval_y product_v5

theorem eval_v6 : toMatrix v6 = decodeRows v6Rows :=
  mul_certificate eval_v5 eval_x product_v6

theorem eval_v7 : toMatrix v7 = decodeRows v7Rows :=
  mul_certificate eval_v6 eval_y product_v7

theorem eval_v8 : toMatrix v8 = decodeRows v8Rows :=
  mul_certificate eval_v7 eval_r product_v8

theorem eval_v9 : toMatrix v9 = decodeRows v9Rows :=
  mul_certificate eval_v8 eval_x product_v9

theorem eval_v10 : toMatrix v10 = decodeRows v10Rows :=
  mul_certificate eval_v9 eval_y product_v10

theorem eval_v11 : toMatrix v11 = decodeRows v11Rows :=
  mul_certificate eval_v10 eval_r product_v11

theorem eval_v12 : toMatrix v12 = decodeRows v12Rows :=
  mul_certificate eval_v11 eval_x product_v12

theorem eval_v13 : toMatrix v13 = decodeRows v13Rows :=
  mul_certificate eval_v12 eval_y product_v13

theorem eval_v14 : toMatrix v14 = decodeRows v14Rows :=
  mul_certificate eval_v13 eval_r product_v14

theorem eval_v15 : toMatrix v15 = decodeRows v15Rows :=
  mul_certificate eval_v14 eval_x product_v15

theorem eval_u2p : toMatrix u2p = decodeRows u2pRows :=
  mul_certificate eval_u15 eval_u15 product_u2p

theorem eval_u4p : toMatrix u4p = decodeRows u4pRows :=
  mul_certificate eval_u2p eval_u2p product_u4p

theorem eval_u8p : toMatrix u8p = decodeRows u8pRows :=
  mul_certificate eval_u4p eval_u4p product_u8p

theorem eval_u10p : toMatrix u10p = decodeRows u10pRows :=
  mul_certificate eval_u8p eval_u2p product_u10p

theorem eval_u11p : toMatrix u11p = decodeRows u11pRows :=
  mul_certificate eval_u10p eval_u15 product_u11p

theorem eval_standardA : toMatrix standardA = decodeRows standardARows :=
  mul_certificate eval_u11p eval_u11p product_standardA

theorem eval_vi : toMatrix vi = decodeRows viRows :=
  inv_certificate eval_v15 product_vi

theorem eval_vu : toMatrix vu = decodeRows vuRows :=
  mul_certificate eval_v15 eval_u11p product_vu

theorem eval_standardB : toMatrix standardB = decodeRows standardBRows :=
  mul_certificate eval_vu eval_vi product_standardB
end Janko4.ThreeConjugates.SecondCertificate
