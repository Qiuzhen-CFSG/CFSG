module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Products5
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Coordinates

/-!
# Evaluation of the ten actual native generators

The checked matrix products are transported through the faithful restriction
of the native representation. All intermediate group words stay named, avoiding
large definitional reductions. Source words: `Words`; arithmetic: `Products0–5`.
-/

public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Janko4.GeneratorCertificates Cardinality KernelCount KernelCount.Relations
open Simplicity.Max1Fusion.KernelOrbits
open NativeRows NativeWords
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis
local notation "ρ" => representation matrixA_mul_self matrixB_pow_four
local notation "x" => localX matrixA_mul_self matrixB_pow_four
local notation "y" => localY matrixA_mul_self matrixB_pow_four
private theorem eval_x : ρ x = decodeRows xRows := representation_x _ _
private theorem eval_ix : ρ x⁻¹ = decodeRows xRows := by
  rw [inv_eq_of_mul_eq_one_left (localX_mul_self matrixA_mul_self matrixB_pow_four)]
  exact eval_x
private theorem eval_y : ρ y = decodeRows yRows := representation_y _ _
private theorem eval_iy : ρ y⁻¹ = decodeRows NativeRows.iyRows :=
  eval_inv ρ eval_y (by rw [decoded_product inverse_y, decode_packedOne])
private theorem eval_d3 : ρ (d3 x y) = decodeRows NativeRows.d3Rows :=
  eval_mul ρ eval_x eval_y (decoded_product product_d3)
private theorem eval_d4 : ρ (d4 x y) = decodeRows NativeRows.d4Rows :=
  eval_mul ρ eval_x eval_iy (decoded_product product_d4)
private theorem eval_d5 : ρ (d5 x y) = decodeRows NativeRows.d5Rows :=
  eval_mul ρ eval_ix eval_y (decoded_product product_d5)
private theorem eval_d6 : ρ (d6 x y) = decodeRows NativeRows.d6Rows :=
  eval_mul ρ eval_ix eval_iy (decoded_product product_d6)
private theorem eval_d7 : ρ (d7 x y) = decodeRows NativeRows.d7Rows :=
  eval_mul ρ eval_d4 eval_d3 (decoded_product product_d7)
private theorem eval_d8 : ρ (d8 x y) = decodeRows NativeRows.d8Rows :=
  eval_mul ρ eval_d5 eval_d5 (decoded_product product_d8)
private theorem eval_d9 : ρ (d9 x y) = decodeRows NativeRows.d9Rows :=
  eval_mul ρ eval_d6 eval_d6 (decoded_product product_d9)
private theorem eval_d10 : ρ (d10 x y) = decodeRows NativeRows.d10Rows :=
  eval_mul ρ eval_d4 eval_d7 (decoded_product product_d10)
private theorem eval_d11 : ρ (d11 x y) = decodeRows NativeRows.d11Rows :=
  eval_mul ρ eval_d3 eval_d3 (decoded_product product_d11)
private theorem eval_d12 : ρ (d12 x y) = decodeRows NativeRows.d12Rows :=
  eval_mul ρ eval_d4 eval_d10 (decoded_product product_d12)
private theorem eval_d13 : ρ (d13 x y) = decodeRows NativeRows.d13Rows :=
  eval_mul ρ eval_d5 eval_d6 (decoded_product product_d13)
private theorem eval_d14 : ρ (d14 x y) = decodeRows NativeRows.d14Rows :=
  eval_mul ρ eval_d3 eval_d7 (decoded_product product_d14)
private theorem eval_d15 : ρ (d15 x y) = decodeRows NativeRows.d15Rows :=
  eval_mul ρ eval_d5 eval_d9 (decoded_product product_d15)
private theorem eval_d16 : ρ (d16 x y) = decodeRows NativeRows.d16Rows :=
  eval_mul ρ eval_d7 eval_d11 (decoded_product product_d16)
private theorem eval_d17 : ρ (d17 x y) = decodeRows NativeRows.d17Rows :=
  eval_mul ρ eval_d13 eval_d8 (decoded_product product_d17)
private theorem eval_d18 : ρ (d18 x y) = decodeRows NativeRows.d18Rows :=
  eval_mul ρ eval_d10 eval_d14 (decoded_product product_d18)
private theorem eval_d19 : ρ (d19 x y) = decodeRows NativeRows.d19Rows :=
  eval_mul ρ eval_d4 eval_d12 (decoded_product product_d19)
private theorem eval_d20 : ρ (d20 x y) = decodeRows NativeRows.d20Rows :=
  eval_mul ρ eval_d6 eval_d8 (decoded_product product_d20)
private theorem eval_d21 : ρ (d21 x y) = decodeRows NativeRows.d21Rows :=
  eval_mul ρ eval_d3 eval_d12 (decoded_product product_d21)
private theorem eval_d22 : ρ (d22 x y) = decodeRows NativeRows.d22Rows :=
  eval_mul ρ eval_d7 eval_d14 (decoded_product product_d22)
private theorem eval_d23 : ρ (d23 x y) = decodeRows NativeRows.d23Rows :=
  eval_mul ρ eval_d8 eval_d8 (decoded_product product_d23)
private theorem eval_d24 : ρ (d24 x y) = decodeRows NativeRows.d24Rows :=
  eval_mul ρ eval_d4 eval_d19 (decoded_product product_d24)
private theorem eval_d25 : ρ (d25 x y) = decodeRows NativeRows.d25Rows :=
  eval_mul ρ eval_d4 eval_iy (decoded_product product_d25)
private theorem eval_d26 : ρ (d26 x y) = decodeRows NativeRows.d26Rows :=
  eval_mul ρ eval_d13 eval_iy (decoded_product product_d26)
private theorem eval_d27 : ρ (d27 x y) = decodeRows NativeRows.d27Rows :=
  eval_mul ρ eval_d11 eval_d16 (decoded_product product_d27)
private theorem eval_d28 : ρ (d28 x y) = decodeRows NativeRows.d28Rows :=
  eval_mul ρ eval_d9 eval_d8 (decoded_product product_d28)
private theorem eval_d29 : ρ (d29 x y) = decodeRows NativeRows.d29Rows :=
  eval_mul ρ eval_d7 eval_d10 (decoded_product product_d29)
private theorem eval_d30 : ρ (d30 x y) = decodeRows NativeRows.d30Rows :=
  eval_mul ρ eval_d4 eval_x (decoded_product product_d30)
private theorem eval_d31 : ρ (d31 x y) = decodeRows NativeRows.d31Rows :=
  eval_mul ρ eval_d11 eval_d21 (decoded_product product_d31)
private theorem eval_d32 : ρ (d32 x y) = decodeRows NativeRows.d32Rows :=
  eval_mul ρ eval_d12 eval_d27 (decoded_product product_d32)
private theorem eval_d33 : ρ (d33 x y) = decodeRows NativeRows.d33Rows :=
  eval_mul ρ eval_d32 eval_d3 (decoded_product product_d33)
private theorem eval_d34 : ρ (d34 x y) = decodeRows NativeRows.d34Rows :=
  eval_mul ρ eval_d33 eval_d13 (decoded_product product_d34)
private theorem eval_d35 : ρ (d35 x y) = decodeRows NativeRows.d35Rows :=
  eval_mul ρ eval_d34 eval_d26 (decoded_product product_d35)
private theorem eval_d36 : ρ (d36 x y) = decodeRows NativeRows.d36Rows :=
  eval_mul ρ eval_d35 eval_d21 (decoded_product product_d36)
private theorem eval_d37 : ρ (d37 x y) = decodeRows NativeRows.d37Rows :=
  eval_mul ρ eval_d36 eval_d11 (decoded_product product_d37)
private theorem eval_d38 : ρ (d38 x y) = decodeRows NativeRows.d38Rows :=
  eval_mul ρ eval_d8 eval_y (decoded_product product_d38)
private theorem eval_d39 : ρ (d39 x y) = decodeRows NativeRows.d39Rows :=
  eval_mul ρ eval_d7 eval_d12 (decoded_product product_d39)
private theorem eval_d40 : ρ (d40 x y) = decodeRows NativeRows.d40Rows :=
  eval_mul ρ eval_d3 eval_x (decoded_product product_d40)
private theorem eval_d41 : ρ (d41 x y) = decodeRows NativeRows.d41Rows :=
  eval_mul ρ eval_d22 eval_d11 (decoded_product product_d41)
private theorem eval_d42 : ρ (d42 x y) = decodeRows NativeRows.d42Rows :=
  eval_mul ρ eval_d17 eval_d15 (decoded_product product_d42)
private theorem eval_d43 : ρ (d43 x y) = decodeRows NativeRows.d43Rows :=
  eval_mul ρ eval_d9 eval_d6 (decoded_product product_d43)
private theorem eval_d44 : ρ (d44 x y) = decodeRows NativeRows.d44Rows :=
  eval_mul ρ eval_d18 eval_d10 (decoded_product product_d44)
private theorem eval_d45 : ρ (d45 x y) = decodeRows NativeRows.d45Rows :=
  eval_mul ρ eval_d16 eval_d14 (decoded_product product_d45)
private theorem eval_p0_0 : ρ (p0_0 x y) = decodeRows NativeRows.p0_0Rows :=
  eval_mul ρ eval_d23 eval_d6 (decoded_product product_p0_0)
private theorem eval_p0_1 : ρ (p0_1 x y) = decodeRows NativeRows.p0_1Rows :=
  eval_mul ρ eval_p0_0 eval_d13 (decoded_product product_p0_1)
private theorem eval_p0_2 : ρ (p0_2 x y) = decodeRows NativeRows.p0_2Rows :=
  eval_mul ρ eval_p0_1 eval_d15 (decoded_product product_p0_2)
private theorem eval_p0_3 : ρ (p0_3 x y) = decodeRows NativeRows.p0_3Rows :=
  eval_mul ρ eval_p0_2 eval_d13 (decoded_product product_p0_3)
private theorem eval_p0_4 : ρ (p0_4 x y) = decodeRows NativeRows.p0_4Rows :=
  eval_mul ρ eval_p0_3 eval_d12 (decoded_product product_p0_4)
private theorem eval_p0_5 : ρ (p0_5 x y) = decodeRows NativeRows.p0_5Rows :=
  eval_mul ρ eval_p0_4 eval_d29 (decoded_product product_p0_5)
private theorem eval_p0_6 : ρ (p0_6 x y) = decodeRows NativeRows.p0_6Rows :=
  eval_mul ρ eval_p0_5 eval_d18 (decoded_product product_p0_6)
private theorem eval_p0_7 : ρ (p0_7 x y) = decodeRows NativeRows.p0_7Rows :=
  eval_mul ρ eval_p0_6 eval_d3 (decoded_product product_p0_7)
private theorem eval_p0_8 : ρ (p0_8 x y) = decodeRows NativeRows.p0_8Rows :=
  eval_mul ρ eval_p0_7 eval_d10 (decoded_product product_p0_8)
private theorem eval_p0_9 : ρ (p0_9 x y) = decodeRows NativeRows.p0_9Rows :=
  eval_mul ρ eval_p0_8 eval_d11 (decoded_product product_p0_9)
private theorem eval_p0_10 : ρ (p0_10 x y) = decodeRows NativeRows.p0_10Rows :=
  eval_mul ρ eval_p0_9 eval_d7 (decoded_product product_p0_10)
private theorem eval_p0_11 : ρ (p0_11 x y) = decodeRows NativeRows.p0_11Rows :=
  eval_mul ρ eval_p0_10 eval_d19 (decoded_product product_p0_11)
private theorem eval_p0_12 : ρ (p0_12 x y) = decodeRows NativeRows.p0_12Rows :=
  eval_mul ρ eval_p0_11 eval_d19 (decoded_product product_p0_12)
private theorem eval_p0_13 : ρ (p0_13 x y) = decodeRows NativeRows.p0_13Rows :=
  eval_mul ρ eval_p0_12 eval_d30 (decoded_product product_p0_13)
private theorem eval_p0_14 : ρ (p0_14 x y) = decodeRows NativeRows.p0_14Rows :=
  eval_mul ρ eval_p0_13 eval_d16 (decoded_product product_p0_14)
private theorem eval_p0_15 : ρ (p0_15 x y) = decodeRows NativeRows.p0_15Rows :=
  eval_mul ρ eval_p0_14 eval_d31 (decoded_product product_p0_15)
private theorem eval_p0_16 : ρ (p0_16 x y) = decodeRows NativeRows.p0_16Rows :=
  eval_mul ρ eval_p0_15 eval_d24 (decoded_product product_p0_16)
private theorem eval_p0_17 : ρ (p0_17 x y) = decodeRows NativeRows.p0_17Rows :=
  eval_mul ρ eval_p0_16 eval_d25 (decoded_product product_p0_17)
private theorem eval_p0_18 : ρ (p0_18 x y) = decodeRows NativeRows.p0_18Rows :=
  eval_mul ρ eval_p0_17 eval_d17 (decoded_product product_p0_18)
private theorem eval_p0_19 : ρ (p0_19 x y) = decodeRows NativeRows.p0_19Rows :=
  eval_mul ρ eval_p0_18 eval_d26 (decoded_product product_p0_19)
private theorem eval_p0_20 : ρ (p0_20 x y) = decodeRows NativeRows.p0_20Rows :=
  eval_mul ρ eval_p0_19 eval_d27 (decoded_product product_p0_20)
private theorem eval_p0_21 : ρ (p0_21 x y) = decodeRows NativeRows.p0_21Rows :=
  eval_mul ρ eval_p0_20 eval_d10 (decoded_product product_p0_21)
private theorem eval_p0_22 : ρ (p0_22 x y) = decodeRows NativeRows.p0_22Rows :=
  eval_mul ρ eval_p0_21 eval_d37 (decoded_product product_p0_22)
private theorem eval_p1_0 : ρ (p1_0 x y) = decodeRows NativeRows.p1_0Rows :=
  eval_mul ρ eval_d23 eval_d38 (decoded_product product_p1_0)
private theorem eval_p1_1 : ρ (p1_1 x y) = decodeRows NativeRows.p1_1Rows :=
  eval_mul ρ eval_p1_0 eval_d7 (decoded_product product_p1_1)
private theorem eval_p1_2 : ρ (p1_2 x y) = decodeRows NativeRows.p1_2Rows :=
  eval_mul ρ eval_p1_1 eval_d39 (decoded_product product_p1_2)
private theorem eval_p1_3 : ρ (p1_3 x y) = decodeRows NativeRows.p1_3Rows :=
  eval_mul ρ eval_p1_2 eval_d40 (decoded_product product_p1_3)
private theorem eval_p1_4 : ρ (p1_4 x y) = decodeRows NativeRows.p1_4Rows :=
  eval_mul ρ eval_p1_3 eval_d7 (decoded_product product_p1_4)
private theorem eval_p1_5 : ρ (p1_5 x y) = decodeRows NativeRows.p1_5Rows :=
  eval_mul ρ eval_p1_4 eval_d41 (decoded_product product_p1_5)
private theorem eval_p1_6 : ρ (p1_6 x y) = decodeRows NativeRows.p1_6Rows :=
  eval_mul ρ eval_p1_5 eval_x (decoded_product product_p1_6)
private theorem eval_p1_7 : ρ (p1_7 x y) = decodeRows NativeRows.p1_7Rows :=
  eval_mul ρ eval_p1_6 eval_d4 (decoded_product product_p1_7)
private theorem eval_p1_8 : ρ (p1_8 x y) = decodeRows NativeRows.p1_8Rows :=
  eval_mul ρ eval_p1_7 eval_d24 (decoded_product product_p1_8)
private theorem eval_p1_9 : ρ (p1_9 x y) = decodeRows NativeRows.p1_9Rows :=
  eval_mul ρ eval_p1_8 eval_y (decoded_product product_p1_9)
private theorem eval_p1_10 : ρ (p1_10 x y) = decodeRows NativeRows.p1_10Rows :=
  eval_mul ρ eval_p1_9 eval_d15 (decoded_product product_p1_10)
private theorem eval_p1_11 : ρ (p1_11 x y) = decodeRows NativeRows.p1_11Rows :=
  eval_mul ρ eval_p1_10 eval_d28 (decoded_product product_p1_11)
private theorem eval_p1_12 : ρ (p1_12 x y) = decodeRows NativeRows.p1_12Rows :=
  eval_mul ρ eval_p1_11 eval_d9 (decoded_product product_p1_12)
private theorem eval_p1_13 : ρ (p1_13 x y) = decodeRows NativeRows.p1_13Rows :=
  eval_mul ρ eval_p1_12 eval_d15 (decoded_product product_p1_13)
private theorem eval_p1_14 : ρ (p1_14 x y) = decodeRows NativeRows.p1_14Rows :=
  eval_mul ρ eval_p1_13 eval_d5 (decoded_product product_p1_14)
private theorem eval_p1_15 : ρ (p1_15 x y) = decodeRows NativeRows.p1_15Rows :=
  eval_mul ρ eval_p1_14 eval_d14 (decoded_product product_p1_15)
private theorem eval_p1_16 : ρ (p1_16 x y) = decodeRows NativeRows.p1_16Rows :=
  eval_mul ρ eval_p1_15 eval_d25 (decoded_product product_p1_16)
private theorem eval_p1_17 : ρ (p1_17 x y) = decodeRows NativeRows.p1_17Rows :=
  eval_mul ρ eval_p1_16 eval_d20 (decoded_product product_p1_17)
private theorem eval_p1_18 : ρ (p1_18 x y) = decodeRows NativeRows.p1_18Rows :=
  eval_mul ρ eval_p1_17 eval_d6 (decoded_product product_p1_18)
private theorem eval_p1_19 : ρ (p1_19 x y) = decodeRows NativeRows.p1_19Rows :=
  eval_mul ρ eval_p1_18 eval_d5 (decoded_product product_p1_19)
private theorem eval_p1_20 : ρ (p1_20 x y) = decodeRows NativeRows.p1_20Rows :=
  eval_mul ρ eval_p1_19 eval_d31 (decoded_product product_p1_20)
private theorem eval_p1_21 : ρ (p1_21 x y) = decodeRows NativeRows.p1_21Rows :=
  eval_mul ρ eval_p1_20 eval_d3 (decoded_product product_p1_21)
private theorem eval_p1_22 : ρ (p1_22 x y) = decodeRows NativeRows.p1_22Rows :=
  eval_mul ρ eval_p1_21 eval_d25 (decoded_product product_p1_22)
private theorem eval_p1_23 : ρ (p1_23 x y) = decodeRows NativeRows.p1_23Rows :=
  eval_mul ρ eval_p1_22 eval_d9 (decoded_product product_p1_23)
private theorem eval_p1_24 : ρ (p1_24 x y) = decodeRows NativeRows.p1_24Rows :=
  eval_mul ρ eval_p1_23 eval_d42 (decoded_product product_p1_24)
private theorem eval_p1_25 : ρ (p1_25 x y) = decodeRows NativeRows.p1_25Rows :=
  eval_mul ρ eval_p1_24 eval_d20 (decoded_product product_p1_25)
private theorem eval_p1_26 : ρ (p1_26 x y) = decodeRows NativeRows.p1_26Rows :=
  eval_mul ρ eval_p1_25 eval_d13 (decoded_product product_p1_26)
private theorem eval_p1_27 : ρ (p1_27 x y) = decodeRows NativeRows.p1_27Rows :=
  eval_mul ρ eval_p1_26 eval_d5 (decoded_product product_p1_27)
private theorem eval_p1_28 : ρ (p1_28 x y) = decodeRows NativeRows.p1_28Rows :=
  eval_mul ρ eval_p1_27 eval_y (decoded_product product_p1_28)
private theorem eval_p1_29 : ρ (p1_29 x y) = decodeRows NativeRows.p1_29Rows :=
  eval_mul ρ eval_p1_28 eval_d7 (decoded_product product_p1_29)
private theorem eval_p1_30 : ρ (p1_30 x y) = decodeRows NativeRows.p1_30Rows :=
  eval_mul ρ eval_p1_29 eval_d4 (decoded_product product_p1_30)
private theorem eval_p1_31 : ρ (p1_31 x y) = decodeRows NativeRows.p1_31Rows :=
  eval_mul ρ eval_p1_30 eval_d4 (decoded_product product_p1_31)
private theorem eval_p1_32 : ρ (p1_32 x y) = decodeRows NativeRows.p1_32Rows :=
  eval_mul ρ eval_p1_31 eval_d43 (decoded_product product_p1_32)
private theorem eval_p1_33 : ρ (p1_33 x y) = decodeRows NativeRows.p1_33Rows :=
  eval_mul ρ eval_p1_32 eval_d15 (decoded_product product_p1_33)
private theorem eval_p1_34 : ρ (p1_34 x y) = decodeRows NativeRows.p1_34Rows :=
  eval_mul ρ eval_p1_33 eval_d20 (decoded_product product_p1_34)
private theorem eval_p1_35 : ρ (p1_35 x y) = decodeRows NativeRows.p1_35Rows :=
  eval_mul ρ eval_p1_34 eval_d17 (decoded_product product_p1_35)
private theorem eval_p2_0 : ρ (p2_0 x y) = decodeRows NativeRows.p2_0Rows :=
  eval_mul ρ eval_d8 eval_d6 (decoded_product product_p2_0)
private theorem eval_p2_1 : ρ (p2_1 x y) = decodeRows NativeRows.p2_1Rows :=
  eval_mul ρ eval_p2_0 eval_d42 (decoded_product product_p2_1)
private theorem eval_p2_2 : ρ (p2_2 x y) = decodeRows NativeRows.p2_2Rows :=
  eval_mul ρ eval_p2_1 eval_d8 (decoded_product product_p2_2)
private theorem eval_p2_3 : ρ (p2_3 x y) = decodeRows NativeRows.p2_3Rows :=
  eval_mul ρ eval_p2_2 eval_d7 (decoded_product product_p2_3)
private theorem eval_p2_4 : ρ (p2_4 x y) = decodeRows NativeRows.p2_4Rows :=
  eval_mul ρ eval_p2_3 eval_d44 (decoded_product product_p2_4)
private theorem eval_p2_5 : ρ (p2_5 x y) = decodeRows NativeRows.p2_5Rows :=
  eval_mul ρ eval_p2_4 eval_d3 (decoded_product product_p2_5)
private theorem eval_p2_6 : ρ (p2_6 x y) = decodeRows NativeRows.p2_6Rows :=
  eval_mul ρ eval_p2_5 eval_d30 (decoded_product product_p2_6)
private theorem eval_p2_7 : ρ (p2_7 x y) = decodeRows NativeRows.p2_7Rows :=
  eval_mul ρ eval_p2_6 eval_d22 (decoded_product product_p2_7)
private theorem eval_p2_8 : ρ (p2_8 x y) = decodeRows NativeRows.p2_8Rows :=
  eval_mul ρ eval_p2_7 eval_d45 (decoded_product product_p2_8)
private theorem eval_p2_9 : ρ (p2_9 x y) = decodeRows NativeRows.p2_9Rows :=
  eval_mul ρ eval_p2_8 eval_d7 (decoded_product product_p2_9)
private theorem eval_p2_10 : ρ (p2_10 x y) = decodeRows NativeRows.p2_10Rows :=
  eval_mul ρ eval_p2_9 eval_d24 (decoded_product product_p2_10)
private theorem eval_p2_11 : ρ (p2_11 x y) = decodeRows NativeRows.p2_11Rows :=
  eval_mul ρ eval_p2_10 eval_d9 (decoded_product product_p2_11)
private theorem eval_p2_12 : ρ (p2_12 x y) = decodeRows NativeRows.p2_12Rows :=
  eval_mul ρ eval_p2_11 eval_d9 (decoded_product product_p2_12)
private theorem eval_p2_13 : ρ (p2_13 x y) = decodeRows NativeRows.p2_13Rows :=
  eval_mul ρ eval_p2_12 eval_d9 (decoded_product product_p2_13)
private theorem eval_p2_14 : ρ (p2_14 x y) = decodeRows NativeRows.p2_14Rows :=
  eval_mul ρ eval_p2_13 eval_iy (decoded_product product_p2_14)
private theorem eval_p2_15 : ρ (p2_15 x y) = decodeRows NativeRows.p2_15Rows :=
  eval_mul ρ eval_p2_14 eval_d17 (decoded_product product_p2_15)
private theorem eval_p2_16 : ρ (p2_16 x y) = decodeRows NativeRows.p2_16Rows :=
  eval_mul ρ eval_p2_15 eval_d20 (decoded_product product_p2_16)
private theorem eval_p2_17 : ρ (p2_17 x y) = decodeRows NativeRows.p2_17Rows :=
  eval_mul ρ eval_p2_16 eval_d38 (decoded_product product_p2_17)
private theorem eval_p2_18 : ρ (p2_18 x y) = decodeRows NativeRows.p2_18Rows :=
  eval_mul ρ eval_p2_17 eval_d12 (decoded_product product_p2_18)
private theorem eval_p2_19 : ρ (p2_19 x y) = decodeRows NativeRows.p2_19Rows :=
  eval_mul ρ eval_p2_18 eval_d9 (decoded_product product_p2_19)
private theorem eval_p2_20 : ρ (p2_20 x y) = decodeRows NativeRows.p2_20Rows :=
  eval_mul ρ eval_p2_19 eval_d28 (decoded_product product_p2_20)
private theorem eval_p2_21 : ρ (p2_21 x y) = decodeRows NativeRows.p2_21Rows :=
  eval_mul ρ eval_p2_20 eval_d6 (decoded_product product_p2_21)
private theorem eval_p2_22 : ρ (p2_22 x y) = decodeRows NativeRows.p2_22Rows :=
  eval_mul ρ eval_p2_21 eval_d15 (decoded_product product_p2_22)
private theorem eval_p2_23 : ρ (p2_23 x y) = decodeRows NativeRows.p2_23Rows :=
  eval_mul ρ eval_p2_22 eval_d43 (decoded_product product_p2_23)
private theorem eval_p3_0 : ρ (p3_0 x y) = decodeRows NativeRows.p3_0Rows :=
  eval_mul ρ eval_iy eval_d11 (decoded_product product_p3_0)
private theorem eval_p3_1 : ρ (p3_1 x y) = decodeRows NativeRows.p3_1Rows :=
  eval_mul ρ eval_p3_0 eval_d18 (decoded_product product_p3_1)
private theorem eval_p3_2 : ρ (p3_2 x y) = decodeRows NativeRows.p3_2Rows :=
  eval_mul ρ eval_p3_1 eval_d6 (decoded_product product_p3_2)
private theorem eval_p3_3 : ρ (p3_3 x y) = decodeRows NativeRows.p3_3Rows :=
  eval_mul ρ eval_p3_2 eval_d11 (decoded_product product_p3_3)
private theorem eval_p3_4 : ρ (p3_4 x y) = decodeRows NativeRows.p3_4Rows :=
  eval_mul ρ eval_p3_3 eval_d11 (decoded_product product_p3_4)
private theorem eval_p3_5 : ρ (p3_5 x y) = decodeRows NativeRows.p3_5Rows :=
  eval_mul ρ eval_p3_4 eval_d10 (decoded_product product_p3_5)
private theorem eval_p3_6 : ρ (p3_6 x y) = decodeRows NativeRows.p3_6Rows :=
  eval_mul ρ eval_p3_5 eval_d18 (decoded_product product_p3_6)
private theorem eval_p3_7 : ρ (p3_7 x y) = decodeRows NativeRows.p3_7Rows :=
  eval_mul ρ eval_p3_6 eval_d44 (decoded_product product_p3_7)
private theorem eval_p3_8 : ρ (p3_8 x y) = decodeRows NativeRows.p3_8Rows :=
  eval_mul ρ eval_p3_7 eval_d40 (decoded_product product_p3_8)
private theorem eval_p3_9 : ρ (p3_9 x y) = decodeRows NativeRows.p3_9Rows :=
  eval_mul ρ eval_p3_8 eval_d45 (decoded_product product_p3_9)
private theorem eval_p3_10 : ρ (p3_10 x y) = decodeRows NativeRows.p3_10Rows :=
  eval_mul ρ eval_p3_9 eval_d39 (decoded_product product_p3_10)
private theorem eval_p3_11 : ρ (p3_11 x y) = decodeRows NativeRows.p3_11Rows :=
  eval_mul ρ eval_p3_10 eval_d41 (decoded_product product_p3_11)
private theorem eval_p3_12 : ρ (p3_12 x y) = decodeRows NativeRows.p3_12Rows :=
  eval_mul ρ eval_p3_11 eval_d4 (decoded_product product_p3_12)
private theorem eval_p3_13 : ρ (p3_13 x y) = decodeRows NativeRows.p3_13Rows :=
  eval_mul ρ eval_p3_12 eval_d15 (decoded_product product_p3_13)
private theorem eval_p3_14 : ρ (p3_14 x y) = decodeRows NativeRows.p3_14Rows :=
  eval_mul ρ eval_p3_13 eval_d8 (decoded_product product_p3_14)
private theorem eval_p3_15 : ρ (p3_15 x y) = decodeRows NativeRows.p3_15Rows :=
  eval_mul ρ eval_p3_14 eval_d9 (decoded_product product_p3_15)
private theorem eval_p3_16 : ρ (p3_16 x y) = decodeRows NativeRows.p3_16Rows :=
  eval_mul ρ eval_p3_15 eval_d20 (decoded_product product_p3_16)
private theorem eval_p3_17 : ρ (p3_17 x y) = decodeRows NativeRows.p3_17Rows :=
  eval_mul ρ eval_p3_16 eval_d28 (decoded_product product_p3_17)
private theorem eval_p3_18 : ρ (p3_18 x y) = decodeRows NativeRows.p3_18Rows :=
  eval_mul ρ eval_p3_17 eval_d17 (decoded_product product_p3_18)
private theorem eval_p3_19 : ρ (p3_19 x y) = decodeRows NativeRows.p3_19Rows :=
  eval_mul ρ eval_p3_18 eval_d22 (decoded_product product_p3_19)
private theorem eval_p3_20 : ρ (p3_20 x y) = decodeRows NativeRows.p3_20Rows :=
  eval_mul ρ eval_p3_19 eval_d29 (decoded_product product_p3_20)
private theorem eval_p3_21 : ρ (p3_21 x y) = decodeRows NativeRows.p3_21Rows :=
  eval_mul ρ eval_p3_20 eval_d37 (decoded_product product_p3_21)
private theorem eval_basis (i : Fin 11) :
    ρ (kernelValue (2^i.val)) = decodeRows (basisRows i) := by
  rw [show kernelValue (2^i.val) = basis matrixA_mul_self matrixB_pow_four i from
    maskValue_basis matrixA_mul_self matrixB_pow_four i]
  exact representation_basis _ _ i
private theorem eval_k5 : ρ (kernelValue 5) = decodeRows NativeRows.k5Rows := by
  rw [show kernelValue 5 = kernelValue 1 * kernelValue 4 from kernelValue_xor 1 4]
  exact eval_mul ρ (eval_basis 0) (eval_basis 2) (decoded_product product_k5)
private theorem eval_k13 : ρ (kernelValue 13) = decodeRows NativeRows.k13Rows := by
  rw [show kernelValue 13 = kernelValue 5 * kernelValue 8 from kernelValue_xor 5 8]
  exact eval_mul ρ eval_k5 (eval_basis 3) (decoded_product product_k13)
private theorem eval_k6 : ρ (kernelValue 6) = decodeRows NativeRows.k6Rows := by
  rw [show kernelValue 6 = kernelValue 2 * kernelValue 4 from kernelValue_xor 2 4]
  exact eval_mul ρ (eval_basis 1) (eval_basis 2) (decoded_product product_k6)
private theorem eval_k22 : ρ (kernelValue 22) = decodeRows NativeRows.k22Rows := by
  rw [show kernelValue 22 = kernelValue 6 * kernelValue 16 from kernelValue_xor 6 16]
  exact eval_mul ρ eval_k6 (eval_basis 4) (decoded_product product_k22)
private theorem eval_k3 : ρ (kernelValue 3) = decodeRows NativeRows.k3Rows := by
  rw [show kernelValue 3 = kernelValue 1 * kernelValue 2 from kernelValue_xor 1 2]
  exact eval_mul ρ (eval_basis 0) (eval_basis 1) (decoded_product product_k3)
private theorem eval_k7 : ρ (kernelValue 7) = decodeRows NativeRows.k7Rows := by
  rw [show kernelValue 7 = kernelValue 3 * kernelValue 4 from kernelValue_xor 3 4]
  exact eval_mul ρ eval_k3 (eval_basis 2) (decoded_product product_k7)
private theorem eval_k15 : ρ (kernelValue 15) = decodeRows NativeRows.k15Rows := by
  rw [show kernelValue 15 = kernelValue 7 * kernelValue 8 from kernelValue_xor 7 8]
  exact eval_mul ρ eval_k7 (eval_basis 3) (decoded_product product_k15)
private theorem eval_k19 : ρ (kernelValue 19) = decodeRows NativeRows.k19Rows := by
  rw [show kernelValue 19 = kernelValue 3 * kernelValue 16 from kernelValue_xor 3 16]
  exact eval_mul ρ eval_k3 (eval_basis 4) (decoded_product product_k19)
private theorem eval_k51 : ρ (kernelValue 51) = decodeRows NativeRows.k51Rows := by
  rw [show kernelValue 51 = kernelValue 19 * kernelValue 32 from kernelValue_xor 19 32]
  exact eval_mul ρ eval_k19 (eval_basis 5) (decoded_product product_k51)
private theorem eval_k9 : ρ (kernelValue 9) = decodeRows NativeRows.k9Rows := by
  rw [show kernelValue 9 = kernelValue 1 * kernelValue 8 from kernelValue_xor 1 8]
  exact eval_mul ρ (eval_basis 0) (eval_basis 3) (decoded_product product_k9)
private theorem eval_k73 : ρ (kernelValue 73) = decodeRows NativeRows.k73Rows := by
  rw [show kernelValue 73 = kernelValue 9 * kernelValue 64 from kernelValue_xor 9 64]
  exact eval_mul ρ eval_k9 (eval_basis 6) (decoded_product product_k73)
private theorem eval_k12 : ρ (kernelValue 12) = decodeRows NativeRows.k12Rows := by
  rw [show kernelValue 12 = kernelValue 4 * kernelValue 8 from kernelValue_xor 4 8]
  exact eval_mul ρ (eval_basis 2) (eval_basis 3) (decoded_product product_k12)
private theorem eval_k140 : ρ (kernelValue 140) = decodeRows NativeRows.k140Rows := by
  rw [show kernelValue 140 = kernelValue 12 * kernelValue 128 from kernelValue_xor 12 128]
  exact eval_mul ρ eval_k12 (eval_basis 7) (decoded_product product_k140)
private theorem eval_k25 : ρ (kernelValue 25) = decodeRows NativeRows.k25Rows := by
  rw [show kernelValue 25 = kernelValue 9 * kernelValue 16 from kernelValue_xor 9 16]
  exact eval_mul ρ eval_k9 (eval_basis 4) (decoded_product product_k25)
private theorem eval_k281 : ρ (kernelValue 281) = decodeRows NativeRows.k281Rows := by
  rw [show kernelValue 281 = kernelValue 25 * kernelValue 256 from kernelValue_xor 25 256]
  exact eval_mul ρ eval_k25 (eval_basis 8) (decoded_product product_k281)
private theorem eval_k515 : ρ (kernelValue 515) = decodeRows NativeRows.k515Rows := by
  rw [show kernelValue 515 = kernelValue 3 * kernelValue 512 from kernelValue_xor 3 512]
  exact eval_mul ρ eval_k3 (eval_basis 9) (decoded_product product_k515)
private theorem eval_k17 : ρ (kernelValue 17) = decodeRows NativeRows.k17Rows := by
  rw [show kernelValue 17 = kernelValue 1 * kernelValue 16 from kernelValue_xor 1 16]
  exact eval_mul ρ (eval_basis 0) (eval_basis 4) (decoded_product product_k17)
private theorem eval_k1041 : ρ (kernelValue 1041) = decodeRows NativeRows.k1041Rows := by
  rw [show kernelValue 1041 = kernelValue 17 * kernelValue 1024 from kernelValue_xor 17 1024]
  exact eval_mul ρ eval_k17 (eval_basis 10) (decoded_product product_k1041)
theorem representation_lift_0 : ρ (lift 0) = decodeRows NativeRows.f0Rows :=
  eval_mul ρ eval_p0_22 eval_k13 (decoded_product product_f0)
theorem representation_lift_1 : ρ (lift 1) = decodeRows NativeRows.f1Rows :=
  eval_mul ρ eval_p1_35 eval_k13 (decoded_product product_f1)
theorem representation_lift_2 : ρ (lift 2) = decodeRows NativeRows.f2Rows :=
  eval_mul ρ eval_p2_23 eval_k22 (decoded_product product_f2)
theorem representation_lift_3 : ρ (lift 3) = decodeRows NativeRows.f3Rows :=
  eval_mul ρ eval_p3_21 eval_k15 (decoded_product product_f3)
@[expose] def liftRows : Fin 4 → Vector ℕ 112 := ![NativeRows.f0Rows, NativeRows.f1Rows, NativeRows.f2Rows, NativeRows.f3Rows]
theorem representation_lift (i : Fin 4) : ρ (lift i) = decodeRows (liftRows i) := by
  fin_cases i
  · exact representation_lift_0
  · exact representation_lift_1
  · exact representation_lift_2
  · exact representation_lift_3
@[expose] def kernelGeneratorRows : Fin 6 → Vector ℕ 112 := ![NativeRows.k51Rows, NativeRows.k73Rows, NativeRows.k140Rows, NativeRows.k281Rows, NativeRows.k515Rows, NativeRows.k1041Rows]
theorem representation_kernelGenerator (i : Fin 6) :
    ρ (kernelGenerator i) = decodeRows (kernelGeneratorRows i) := by
  fin_cases i
  · exact eval_k51
  · exact eval_k73
  · exact eval_k140
  · exact eval_k281
  · exact eval_k515
  · exact eval_k1041
end Janko4.LocalStructure.LinearFive
