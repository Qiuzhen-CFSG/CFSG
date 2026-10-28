module

public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Products
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Relations in the concrete Rudvalis covering matrices

The ATLAS matrices have orders dividing four, their product has thirteenth
power one, and the word ABABB has twenty-ninth power one. The first generator
squares to minus the identity. These are relations in concrete matrices,
not a presentation or an identification with the Rudvalis quotient.
-/

namespace Rudvalis.Multiplier.DoubleCover
public section

theorem matrixOne_eq : matrixOne = 1 := by decide +kernel

theorem matrixNegOne_eq : matrixNegOne = -1 := by decide +kernel

theorem matrixA_sq : matrixA ^ 2 = -1 := by
  rw [pow_two, product_0, matrixNegOne_eq]

theorem matrixA_fourth : matrixA ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, matrixA_sq]
  exact neg_one_sq

theorem matrixB_fourth : matrixB ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, pow_two matrixB, product_1,
    pow_two, product_2, matrixOne_eq]

theorem matrixAB_thirteenth : (matrixA * matrixB) ^ 13 = 1 := by
  rw [product_3]
  have h2 : ab ^ 2 = ab2 := by rw [pow_two, product_4]
  have h4 : ab ^ 4 = ab4 := by rw [show 4 = 2 * 2 from rfl, pow_mul, h2, pow_two, product_5]
  have h8 : ab ^ 8 = ab8 := by rw [show 8 = 4 * 2 from rfl, pow_mul, h4, pow_two, product_6]
  have h12 : ab ^ 12 = ab12 := by rw [show 12 = 8 + 4 from rfl, pow_add, h8, h4, product_7]
  rw [show 13 = 12 + 1 from rfl, pow_succ, h12, product_8, matrixOne_eq]

theorem matrixW_twentyNinth : (matrixA * matrixB * matrixA * matrixB * matrixB) ^ 29 = 1 := by
  rw [product_3, product_9, product_10, product_11]
  have h2 : w ^ 2 = w2 := by rw [pow_two, product_12]
  have h4 : w ^ 4 = w4 := by rw [show 4 = 2 * 2 from rfl, pow_mul, h2, pow_two, product_13]
  have h8 : w ^ 8 = w8 := by rw [show 8 = 4 * 2 from rfl, pow_mul, h4, pow_two, product_14]
  have h16 : w ^ 16 = w16 := by rw [show 16 = 8 * 2 from rfl, pow_mul, h8, pow_two, product_15]
  have h24 : w ^ 24 = w24 := by rw [show 24 = 16 + 8 from rfl, pow_add, h16, h8, product_16]
  have h28 : w ^ 28 = w28 := by
    calc
      _ = w ^ 24 * w ^ 4 := pow_add w 24 4
      _ = w28 := by rw [h24, h4, product_17]
  rw [show 29 = 28 + 1 from rfl, pow_succ, h28, product_18, matrixOne_eq]

/-- First ATLAS matrix as an invertible matrix, with inverse A cubed. -/
@[expose] def A : Matˣ where
  val := matrixA
  inv := matrixA ^ 3
  val_inv := by rw [← pow_succ']; exact matrixA_fourth
  inv_val := by rw [← pow_succ]; exact matrixA_fourth

/-- Second ATLAS matrix as an invertible matrix, with inverse B cubed. -/
@[expose] def B : Matˣ where
  val := matrixB
  inv := matrixB ^ 3
  val_inv := by rw [← pow_succ']; exact matrixB_fourth
  inv_val := by rw [← pow_succ]; exact matrixB_fourth

theorem A_sq : A ^ 2 = -1 := Units.ext matrixA_sq

theorem A_fourth : A ^ 4 = 1 := Units.ext matrixA_fourth

theorem B_fourth : B ^ 4 = 1 := Units.ext matrixB_fourth

theorem AB_thirteenth : (A * B) ^ 13 = 1 := Units.ext matrixAB_thirteenth

theorem W_twentyNinth : (A * B * A * B * B) ^ 29 = 1 := Units.ext matrixW_twentyNinth

end
end Rudvalis.Multiplier.DoubleCover
