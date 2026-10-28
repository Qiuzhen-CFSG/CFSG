module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Evaluation
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Products.Part4
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Products.Part5
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Products.Part6
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Products.Part7
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Products.Part8

/-!
# Multiplication, separation, and conjugation of the normal eight

The packed certificates give the full multiplication table and the right
conjugation permutations of the eight actual words. Three entries of the first
matrix row distinguish all eight words. These identities are the finite input
used to construct an elementary subgroup normal in the literal max4.
-/

public section

namespace Janko4.LocalStructure.SymmetricLinear.NormalEight
open Janko4.GeneratorCertificates

private lemma decoded_product {a b c : Vector ℕ 112} (h : packedMul a b = c) :
    decodeRows a * decodeRows b = decodeRows c := by
  rw [← decode_packedMul, h]

private theorem decoded_table (i j : Fin 8) :
    decodeRows (elementRows i) * decodeRows (elementRows j) =
      decodeRows (elementRows (productIndex i j)) := by
  fin_cases i <;> fin_cases j
  · change decodeRows packedOne * decodeRows packedOne = decodeRows packedOne
    rw [decode_packedOne, one_mul]
  · change decodeRows packedOne * decodeRows seedPower6Rows = decodeRows seedPower6Rows
    rw [decode_packedOne, one_mul]
  · change decodeRows packedOne * decodeRows e2Rows = decodeRows e2Rows
    rw [decode_packedOne, one_mul]
  · change decodeRows packedOne * decodeRows e3Rows = decodeRows e3Rows
    rw [decode_packedOne, one_mul]
  · change decodeRows packedOne * decodeRows e4Rows = decodeRows e4Rows
    rw [decode_packedOne, one_mul]
  · change decodeRows packedOne * decodeRows e5Rows = decodeRows e5Rows
    rw [decode_packedOne, one_mul]
  · change decodeRows packedOne * decodeRows e6Rows = decodeRows e6Rows
    rw [decode_packedOne, one_mul]
  · change decodeRows packedOne * decodeRows e7Rows = decodeRows e7Rows
    rw [decode_packedOne, one_mul]
  · change decodeRows seedPower6Rows * decodeRows packedOne = decodeRows seedPower6Rows
    rw [decode_packedOne, mul_one]
  · exact decoded_product mul_1_1
  · exact decoded_product mul_1_2
  · exact decoded_product mul_1_3
  · exact decoded_product mul_1_4
  · exact decoded_product mul_1_5
  · exact decoded_product mul_1_6
  · exact decoded_product mul_1_7
  · change decodeRows e2Rows * decodeRows packedOne = decodeRows e2Rows
    rw [decode_packedOne, mul_one]
  · exact decoded_product mul_2_1
  · exact decoded_product mul_2_2
  · exact decoded_product mul_2_3
  · exact decoded_product mul_2_4
  · exact decoded_product mul_2_5
  · exact decoded_product mul_2_6
  · exact decoded_product mul_2_7
  · change decodeRows e3Rows * decodeRows packedOne = decodeRows e3Rows
    rw [decode_packedOne, mul_one]
  · exact decoded_product mul_3_1
  · exact decoded_product mul_3_2
  · exact decoded_product mul_3_3
  · exact decoded_product mul_3_4
  · exact decoded_product mul_3_5
  · exact decoded_product mul_3_6
  · exact decoded_product mul_3_7
  · change decodeRows e4Rows * decodeRows packedOne = decodeRows e4Rows
    rw [decode_packedOne, mul_one]
  · exact decoded_product mul_4_1
  · exact decoded_product mul_4_2
  · exact decoded_product mul_4_3
  · exact decoded_product mul_4_4
  · exact decoded_product mul_4_5
  · exact decoded_product mul_4_6
  · exact decoded_product mul_4_7
  · change decodeRows e5Rows * decodeRows packedOne = decodeRows e5Rows
    rw [decode_packedOne, mul_one]
  · exact decoded_product mul_5_1
  · exact decoded_product mul_5_2
  · exact decoded_product mul_5_3
  · exact decoded_product mul_5_4
  · exact decoded_product mul_5_5
  · exact decoded_product mul_5_6
  · exact decoded_product mul_5_7
  · change decodeRows e6Rows * decodeRows packedOne = decodeRows e6Rows
    rw [decode_packedOne, mul_one]
  · exact decoded_product mul_6_1
  · exact decoded_product mul_6_2
  · exact decoded_product mul_6_3
  · exact decoded_product mul_6_4
  · exact decoded_product mul_6_5
  · exact decoded_product mul_6_6
  · exact decoded_product mul_6_7
  · change decodeRows e7Rows * decodeRows packedOne = decodeRows e7Rows
    rw [decode_packedOne, mul_one]
  · exact decoded_product mul_7_1
  · exact decoded_product mul_7_2
  · exact decoded_product mul_7_3
  · exact decoded_product mul_7_4
  · exact decoded_product mul_7_5
  · exact decoded_product mul_7_6
  · exact decoded_product mul_7_7

theorem element_mul (i j : Fin 8) : element i * element j = element (productIndex i j) := by
  apply matrix_injective
  rw [map_mul, matrix_element, matrix_element, matrix_element, decoded_table]

theorem productIndex_self (i : Fin 8) : productIndex i i = 0 := by
  revert i
  decide +kernel

theorem productIndex_comm (i j : Fin 8) : productIndex i j = productIndex j i := by
  revert i j
  decide +kernel

theorem element_sq (i : Fin 8) : element i * element i = 1 := by
  rw [element_mul, productIndex_self, element_zero]

theorem element_comm (i j : Fin 8) : element i * element j = element j * element i := by
  rw [element_mul, element_mul, productIndex_comm]

private def signature (r : Vector ℕ 112) : Bool × Bool × Bool :=
  ((r.get 0).testBit 2, (r.get 0).testBit 14, (r.get 0).testBit 46)

private theorem signature_injective :
    Function.Injective (fun i : Fin 8 => signature (elementRows i)) := by
  have h : (fun i : Fin 8 => signature (elementRows i)) =
      ![(false, false, false), (true, false, true), (false, true, false),
        (false, true, true), (true, false, false), (false, false, true),
        (true, true, false), (true, true, true)] := by
    funext i
    fin_cases i
    · change signature packedOne = _
      simp only [signature, packedOne, get_ofFn]
      decide +kernel
    all_goals decide +kernel
  rw [h]
  decide +kernel

private theorem bit_injective {b c : Bool}
    (h : (if b then (1 : ZMod 2) else 0) = if c then 1 else 0) : b = c := by
  cases b <;> cases c <;> simp_all

private theorem signature_eq_of_decodeRows_eq {r s : Vector ℕ 112}
    (h : decodeRows r = decodeRows s) : signature r = signature s := by
  apply Prod.ext
  · exact bit_injective (congrFun (congrFun h 0) 2)
  · apply Prod.ext
    · exact bit_injective (congrFun (congrFun h 0) 14)
    · exact bit_injective (congrFun (congrFun h 0) 46)

theorem element_injective : Function.Injective element := by
  intro i j hij
  apply signature_injective
  apply signature_eq_of_decodeRows_eq
  rw [← matrix_element, ← matrix_element, hij]

private lemma conjugate_eq {a g c : max4Subgroup}
    (h : matrix a * matrix g = matrix g * matrix c) : g⁻¹ * a * g = c := by
  apply matrix_injective
  calc
    matrix (g⁻¹ * a * g) = matrix g⁻¹ * (matrix a * matrix g) := by
      rw [map_mul, map_mul, mul_assoc]
    _ = matrix c := by
      rw [h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem element_conj_x (i : Fin 8) :
    x⁻¹ * element i * x = element (actionX i) := by
  fin_cases i
  · change x⁻¹ * 1 * x = 1
    simp
  · apply conjugate_eq
    rw [matrix_element, matrix_x, matrix_element]
    exact (decoded_product action_x_1_left).trans
      (decoded_product action_x_1_right).symm
  · apply conjugate_eq
    rw [matrix_element, matrix_x, matrix_element]
    exact (decoded_product action_x_2_left).trans
      (decoded_product action_x_2_right).symm
  · apply conjugate_eq
    rw [matrix_element, matrix_x, matrix_element]
    exact (decoded_product action_x_3_left).trans
      (decoded_product action_x_3_right).symm
  · apply conjugate_eq
    rw [matrix_element, matrix_x, matrix_element]
    exact (decoded_product action_x_4_left).trans
      (decoded_product action_x_4_right).symm
  · apply conjugate_eq
    rw [matrix_element, matrix_x, matrix_element]
    exact (decoded_product action_x_5_left).trans
      (decoded_product action_x_5_right).symm
  · apply conjugate_eq
    rw [matrix_element, matrix_x, matrix_element]
    exact (decoded_product action_x_6_left).trans
      (decoded_product action_x_6_right).symm
  · apply conjugate_eq
    rw [matrix_element, matrix_x, matrix_element]
    exact (decoded_product action_x_7_left).trans
      (decoded_product action_x_7_right).symm
theorem element_conj_y (i : Fin 8) :
    y⁻¹ * element i * y = element (actionY i) := by
  fin_cases i
  · change y⁻¹ * 1 * y = 1
    simp
  · apply conjugate_eq
    rw [matrix_element, matrix_y, matrix_element]
    exact (decoded_product action_y_1_left).trans
      (decoded_product action_y_1_right).symm
  · apply conjugate_eq
    rw [matrix_element, matrix_y, matrix_element]
    exact (decoded_product action_y_2_left).trans
      (decoded_product action_y_2_right).symm
  · apply conjugate_eq
    rw [matrix_element, matrix_y, matrix_element]
    exact (decoded_product action_y_3_left).trans
      (decoded_product action_y_3_right).symm
  · apply conjugate_eq
    rw [matrix_element, matrix_y, matrix_element]
    exact (decoded_product action_y_4_left).trans
      (decoded_product action_y_4_right).symm
  · apply conjugate_eq
    rw [matrix_element, matrix_y, matrix_element]
    exact (decoded_product action_y_5_left).trans
      (decoded_product action_y_5_right).symm
  · apply conjugate_eq
    rw [matrix_element, matrix_y, matrix_element]
    exact (decoded_product action_y_6_left).trans
      (decoded_product action_y_6_right).symm
  · apply conjugate_eq
    rw [matrix_element, matrix_y, matrix_element]
    exact (decoded_product action_y_7_left).trans
      (decoded_product action_y_7_right).symm

end Janko4.LocalStructure.SymmetricLinear.NormalEight
