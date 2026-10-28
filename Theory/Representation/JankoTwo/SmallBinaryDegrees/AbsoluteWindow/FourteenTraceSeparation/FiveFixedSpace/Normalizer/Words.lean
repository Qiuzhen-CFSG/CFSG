module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
/-!
# Checked words for an elementary five-plane in the ATLAS J₂ carrier

The saved GAP words are interpreted in the actual standard generators, using
Lean's left composition convention. Small permutation tables certify their
orders, commutation, and cubic conjugation equations. Evaluating the 25
products at point zero proves independence and excludes nonidentity fixed
points of the cubic action. Every table and comparison is kernel checked.

Source: Wilson et al., ATLAS of Finite Group Representations, J2G1-p100B0,
with attribution and original generators retained alongside `GeneratorPair`.
The words were obtained from the ATLAS local subgroup 5²:D₁₂; the saved GAP
witnesses are used only as data, not as a proof or an order certificate for J₂.
-/

open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveNormalizer.Words
set_option maxRecDepth 20000
private def xWord {G : Type*} [Group G] (a b : G) : G :=
  (a * b * a * b⁻¹) ^ 4 * a * b⁻¹ * (a * b) ^ 3 * (a⁻¹ * b⁻¹) ^ 2 * a⁻¹ * b * (a⁻¹ * b * a⁻¹ * b⁻¹) ^ 2 * (a⁻¹ * b * (a⁻¹ * b⁻¹) ^ 2 * a⁻¹ * b) ^ 2 * (a⁻¹ * b⁻¹) ^ 2 * a⁻¹
private def nWord {G : Type*} [Group G] (a b : G) : G :=
  b⁻¹ * (a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b) ^ 2 * a⁻¹ * b⁻¹ * (a⁻¹ * b) ^ 2 * b * a * b * (a * b⁻¹ * (a * b) ^ 2 * a * b⁻¹) ^ 2 * (a * b * a * b⁻¹) ^ 2 * a * b⁻¹ * (a * b) ^ 3 * (a⁻¹ * b * a⁻¹ * b⁻¹) ^ 2 * (a⁻¹ * b⁻¹ * (a⁻¹ * b) ^ 2 * a⁻¹) ^ 2 * (b⁻¹ * a⁻¹) ^ 2 * b * a⁻¹ * b⁻¹ * a⁻¹
private def xValues : Fin 100 → Fin 100 :=
  ![98, 36, 12, 10, 38, 53, 95, 88, 44, 48, 13, 79, 8, 19, 87, 18, 9, 37, 93, 89,
    47, 75, 26, 34, 41, 73, 96, 16, 30, 49, 31, 97, 43, 81, 39, 67, 22, 57, 46, 0,
    85, 84, 70, 74, 61, 94, 99, 45, 54, 33, 92, 86, 58, 7, 27, 25, 29, 83, 80, 76,
    20, 2, 71, 4, 78, 28, 5, 55, 40, 50, 82, 32, 17, 35, 62, 15, 52, 68, 51, 24,
    59, 56, 6, 72, 11, 91, 90, 69, 66, 3, 64, 77, 14, 21, 60, 42, 1, 65, 23, 63]
private def xInvValues : Fin 100 → Fin 100 :=
  ![39, 96, 61, 89, 63, 66, 82, 53, 12, 16, 3, 84, 2, 10, 92, 75, 27, 72, 15, 13,
    60, 93, 36, 98, 79, 55, 22, 54, 65, 56, 28, 30, 71, 49, 23, 73, 1, 17, 4, 34,
    68, 24, 95, 32, 8, 47, 38, 20, 9, 29, 69, 78, 76, 5, 48, 67, 81, 37, 52, 80,
    94, 44, 74, 99, 90, 97, 88, 35, 77, 87, 42, 62, 83, 25, 43, 21, 59, 91, 64, 11,
    58, 33, 70, 57, 41, 40, 51, 14, 7, 19, 86, 85, 50, 18, 45, 6, 26, 31, 0, 46]
private def xTable : Equiv.Perm (Fin 100) where
  toFun := xValues
  invFun := xInvValues
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def nValues : Fin 100 → Fin 100 :=
  ![2, 40, 34, 45, 52, 54, 96, 88, 44, 68, 43, 75, 10, 39, 37, 30, 5, 15, 18, 13,
    3, 41, 9, 74, 79, 63, 70, 42, 93, 33, 17, 84, 89, 86, 0, 80, 36, 83, 73, 19,
    48, 92, 95, 12, 47, 20, 49, 8, 1, 99, 97, 25, 59, 6, 16, 81, 35, 24, 55, 4,
    23, 32, 62, 51, 78, 31, 26, 67, 22, 50, 66, 98, 28, 90, 60, 87, 64, 85, 76, 57,
    56, 58, 77, 14, 65, 82, 29, 11, 91, 61, 38, 7, 21, 72, 71, 27, 53, 69, 94, 46]
private def nInvValues : Fin 100 → Fin 100 :=
  ![34, 48, 0, 20, 59, 16, 53, 91, 47, 22, 12, 87, 43, 19, 83, 17, 54, 30, 18, 39,
    45, 92, 68, 60, 57, 51, 66, 95, 72, 86, 15, 65, 61, 29, 2, 56, 36, 14, 90, 13,
    1, 21, 27, 10, 8, 3, 99, 44, 40, 46, 69, 63, 4, 96, 5, 58, 80, 79, 81, 52,
    74, 89, 62, 25, 76, 84, 70, 67, 9, 97, 26, 94, 93, 38, 23, 11, 78, 82, 64, 24,
    35, 55, 85, 37, 31, 77, 33, 75, 7, 32, 73, 88, 41, 28, 98, 42, 6, 50, 71, 49]
private def nTable : Equiv.Perm (Fin 100) where
  toFun := nValues
  invFun := nInvValues
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def yValues : Fin 100 → Fin 100 :=
  ![43, 77, 13, 98, 81, 95, 48, 70, 89, 1, 23, 17, 19, 34, 79, 65, 96, 18, 28, 39,
    12, 31, 40, 62, 57, 59, 85, 26, 92, 55, 14, 87, 20, 73, 71, 52, 68, 93, 56, 32,
    5, 83, 27, 47, 3, 44, 29, 8, 36, 25, 84, 38, 78, 42, 22, 80, 67, 21, 51, 90,
    2, 10, 94, 33, 63, 50, 6, 58, 66, 41, 16, 60, 15, 76, 45, 97, 64, 88, 4, 37,
    86, 35, 9, 75, 72, 53, 46, 24, 82, 0, 99, 7, 11, 30, 61, 54, 91, 69, 74, 49]
private def yInvValues : Fin 100 → Fin 100 :=
  ![89, 9, 60, 44, 78, 40, 66, 91, 47, 82, 61, 92, 20, 2, 30, 72, 70, 11, 17, 12,
    32, 57, 54, 10, 87, 49, 27, 42, 18, 46, 93, 21, 39, 63, 13, 81, 48, 79, 51, 19,
    22, 69, 53, 0, 45, 74, 86, 43, 6, 99, 65, 58, 35, 85, 95, 29, 38, 24, 67, 25,
    71, 94, 23, 64, 76, 15, 68, 56, 36, 97, 7, 34, 84, 33, 98, 83, 73, 1, 52, 14,
    55, 4, 88, 41, 50, 26, 80, 31, 77, 8, 59, 96, 28, 37, 62, 5, 16, 75, 3, 90]
private def yTable : Equiv.Perm (Fin 100) where
  toFun := yValues
  invFun := yInvValues
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private theorem xWord_table : xWord tableA tableB = xTable := by
  apply Equiv.ext
  decide +kernel
private theorem nWord_table : nWord tableA tableB = nTable := by
  apply Equiv.ext
  decide +kernel

private theorem yTable_eq : nTable⁻¹ * xTable * nTable = yTable := by decide +kernel

private theorem xTable_five : xTable ^ 5 = 1 := by decide +kernel
private theorem yTable_five : yTable ^ 5 = 1 := by decide +kernel
private theorem nTable_three : nTable ^ 3 = 1 := by decide +kernel
private theorem tables_commute : xTable * yTable = yTable * xTable := by decide +kernel
private theorem second_conjugate : nTable⁻¹ * yTable * nTable = xTable⁻¹ * yTable⁻¹ := by
  decide +kernel

private def position : Fin 5 → Fin 5 → Fin 100 :=
  ![![0, 43, 47, 8, 89],
    ![98, 74, 45, 44, 3],
    ![23, 62, 94, 61, 10],
    ![34, 71, 60, 2, 13],
    ![39, 32, 20, 12, 19]]

private theorem position_correct : ∀ i j : Fin 5,
    (xTable ^ i.val * yTable ^ j.val) (0 : Fin 100) = position i j := by
  decide +kernel

private theorem position_injective : ∀ i j k l : Fin 5,
    position i j = position k l → i = k ∧ j = l := by
  decide +kernel

private theorem table_coordinate_injective (i j k l : Fin 5)
    (h : (xTable ^ i.val * yTable ^ j.val) (0 : Fin 100) =
      (xTable ^ k.val * yTable ^ l.val) (0 : Fin 100)) : i = k ∧ j = l := by
  rw [position_correct, position_correct] at h
  exact position_injective i j k l h

private theorem table_fixed_coordinate : ∀ i j : Fin 5,
    (nTable⁻¹ * (xTable ^ i.val * yTable ^ j.val) * nTable) (0 : Fin 100) =
      (xTable ^ i.val * yTable ^ j.val) (0 : Fin 100) → i = 0 ∧ j = 0 := by
  decide +kernel


public def x : Carrier := xWord a b
public def n : Carrier := nWord a b
@[expose] public def y : Carrier := n⁻¹ * x * n

private theorem x_coe : (x : Equiv.Perm (Fin 100)) = xTable := by
  change xWord generatorA generatorB = xTable
  rw [generatorA_eq_table, generatorB_eq_table, xWord_table]
private theorem n_coe : (n : Equiv.Perm (Fin 100)) = nTable := by
  change nWord generatorA generatorB = nTable
  rw [generatorA_eq_table, generatorB_eq_table, nWord_table]
private theorem y_coe : (y : Equiv.Perm (Fin 100)) = yTable := by
  change (n : Equiv.Perm (Fin 100))⁻¹ * x * n = yTable
  rw [n_coe, x_coe, yTable_eq]

public theorem x_five : x ^ 5 = 1 := by
  apply Subtype.ext
  change (x : Equiv.Perm (Fin 100)) ^ 5 = 1
  rw [x_coe, xTable_five]
public theorem y_five : y ^ 5 = 1 := by
  apply Subtype.ext
  change (y : Equiv.Perm (Fin 100)) ^ 5 = 1
  rw [y_coe, yTable_five]
public theorem n_three : n ^ 3 = 1 := by
  apply Subtype.ext
  change (n : Equiv.Perm (Fin 100)) ^ 3 = 1
  rw [n_coe, nTable_three]
public theorem xy_commute : Commute x y := by
  apply Subtype.ext
  change (x : Equiv.Perm (Fin 100)) * y = y * x
  rw [x_coe, y_coe, tables_commute]
public theorem conj_y : n⁻¹ * y * n = x⁻¹ * y⁻¹ := by
  apply Subtype.ext
  change (n : Equiv.Perm (Fin 100))⁻¹ * y * n = (x : Equiv.Perm (Fin 100))⁻¹ * (y : Equiv.Perm (Fin 100))⁻¹
  rw [n_coe, x_coe, y_coe, second_conjugate]


public theorem conj_x : n⁻¹ * x * n = y := rfl

public theorem coordinate_injective (i j k l : Fin 5)
    (h : ((x : Equiv.Perm (Fin 100)) ^ i.val * (y : Equiv.Perm (Fin 100)) ^ j.val) 0 =
      ((x : Equiv.Perm (Fin 100)) ^ k.val * (y : Equiv.Perm (Fin 100)) ^ l.val) 0) :
    i = k ∧ j = l := by
  rw [x_coe, y_coe] at h
  exact table_coordinate_injective i j k l h

public theorem fixed_coordinate (i j : Fin 5)
    (h : ((n : Equiv.Perm (Fin 100))⁻¹ *
        ((x : Equiv.Perm (Fin 100)) ^ i.val * (y : Equiv.Perm (Fin 100)) ^ j.val) * n) 0 =
      ((x : Equiv.Perm (Fin 100)) ^ i.val * (y : Equiv.Perm (Fin 100)) ^ j.val) 0) :
    i = 0 ∧ j = 0 := by
  rw [x_coe, y_coe, n_coe] at h
  exact table_fixed_coordinate i j h

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveNormalizer.Words
