module

public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords

/-!
# Split-root identities for the first Ree replacement

The first seven main curves centralize both central curves y₃ and y₅.
The eighth curve acts by y₃(a) ↦ y₃(a)y₅(au). These identities follow
from the actual characteristic-two F₄ matrix relations, uniformly in the field.
Source: GLS3 Table 2.4, 2.4.5(d), 2.4.6 and Lemma 3.3.9.
-/

public section
noncomputable section
namespace ReeF4.ReplacementCentralizerRoots
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations MatrixRelations.LongCommutators
open Theory.AlgebraicGroup.StandardRootSystem
open NormalizedRootCentralizers.CenterExponent.OuterElimination

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (longRoot_isLong i), halfFrobenius]

private theorem word_0 (m : ℕ) (t : CoefficientField m) :
    rootWord m 0 t = X m 0 t * X m 1 (halfFrobenius m t) * X m 2 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_1 (m : ℕ) (t : CoefficientField m) :
    rootWord m 1 t = X m 4 t * X m 5 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change (X m 4 t * X m 5 (halfFrobenius m t)) * 1 = _
  exact mul_one _

private theorem word_2 (m : ℕ) (t : CoefficientField m) :
    rootWord m 2 t = X m 6 t * X m 7 (halfFrobenius m t) * X m 8 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_3 (m : ℕ) (t : CoefficientField m) :
    rootWord m 3 t = X m 10 t * X m 11 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change (X m 10 t * X m 11 (halfFrobenius m t)) * 1 = _
  exact mul_one _

private theorem word_4 (m : ℕ) (t : CoefficientField m) :
    rootWord m 4 t = X m 12 t * X m 13 (halfFrobenius m t) * X m 14 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_5 (m : ℕ) (t : CoefficientField m) :
    rootWord m 5 t = X m 16 t * X m 17 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change (X m 16 t * X m 17 (halfFrobenius m t)) * 1 = _
  exact mul_one _

private theorem word_6 (m : ℕ) (t : CoefficientField m) :
    rootWord m 6 t = X m 18 t * X m 19 (halfFrobenius m t) * X m 20 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_7 (m : ℕ) (t : CoefficientField m) :
    rootWord m 7 t = X m 22 t * X m 23 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change (X m 22 t * X m 23 (halfFrobenius m t)) * 1 = _
  exact mul_one _

private theorem central_2 (m : ℕ) (t : CoefficientField m) :
    centralWord m 2 t = X m 9 t * X m 8 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]
  rfl

private theorem central_4 (m : ℕ) (t : CoefficientField m) :
    centralWord m 4 t = X m 15 t * X m 14 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]
  rfl

attribute [local irreducible] X

theorem main_central_2 (m : ℕ) (i : Fin 8) (hi : i ≠ 7) (a b : CoefficientField m) :
    Commute (rootWord m i a) (centralWord m 2 b) := by
  fin_cases i
  · change Commute (rootWord m 0 a) (centralWord m 2 b)
    rw [word_0 m a, central_2 m b]
    exact (((xc m 0 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 0 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 1 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 1 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))).mul_left ((xc m 2 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) b).mul_right
      (xc m 2 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 1 a) (centralWord m 2 b)
    rw [word_1 m a, central_2 m b]
    exact ((xc m 4 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 4 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 5 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 5 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 2 a) (centralWord m 2 b)
    rw [word_2 m a, central_2 m b]
    exact (((xc m 6 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 6 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 7 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 7 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))).mul_left ((xc m 8 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) b).mul_right
      (xc m 8 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 3 a) (centralWord m 2 b)
    rw [word_3 m a, central_2 m b]
    exact ((xc m 10 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 10 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 11 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 11 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 4 a) (centralWord m 2 b)
    rw [word_4 m a, central_2 m b]
    exact (((xc m 12 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 12 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 13 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 13 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))).mul_left ((xc m 14 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) b).mul_right
      (xc m 14 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 5 a) (centralWord m 2 b)
    rw [word_5 m a, central_2 m b]
    exact ((xc m 16 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 16 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 17 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 17 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 6 a) (centralWord m 2 b)
    rw [word_6 m a, central_2 m b]
    exact (((xc m 18 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 18 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 19 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 19 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))).mul_left ((xc m 20 9 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) b).mul_right
      (xc m 20 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) (halfFrobenius m b)))
  · exact (hi rfl).elim

theorem main_central_4 (m : ℕ) (i : Fin 8) (a b : CoefficientField m) :
    Commute (rootWord m i a) (centralWord m 4 b) := by
  fin_cases i
  · change Commute (rootWord m 0 a) (centralWord m 4 b)
    rw [word_0 m a, central_4 m b]
    exact (((xc m 0 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 0 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 1 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 1 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))).mul_left ((xc m 2 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) b).mul_right
      (xc m 2 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 1 a) (centralWord m 4 b)
    rw [word_1 m a, central_4 m b]
    exact ((xc m 4 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 4 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 5 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 5 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 2 a) (centralWord m 4 b)
    rw [word_2 m a, central_4 m b]
    exact (((xc m 6 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 6 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 7 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 7 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))).mul_left ((xc m 8 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) b).mul_right
      (xc m 8 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 3 a) (centralWord m 4 b)
    rw [word_3 m a, central_4 m b]
    exact ((xc m 10 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 10 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 11 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 11 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 4 a) (centralWord m 4 b)
    rw [word_4 m a, central_4 m b]
    exact (((xc m 12 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 12 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 13 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 13 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))).mul_left ((xc m 14 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) b).mul_right
      (xc m 14 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 5 a) (centralWord m 4 b)
    rw [word_5 m a, central_4 m b]
    exact ((xc m 16 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 16 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 17 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 17 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 6 a) (centralWord m 4 b)
    rw [word_6 m a, central_4 m b]
    exact (((xc m 18 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 18 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 19 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 19 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))).mul_left ((xc m 20 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) b).mul_right
      (xc m 20 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * halfFrobenius m a) (halfFrobenius m b)))
  · change Commute (rootWord m 7 a) (centralWord m 4 b)
    rw [word_7 m a, central_4 m b]
    exact ((xc m 22 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
      (xc m 22 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left ((xc m 23 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 23 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))

theorem central_commute (m : ℕ) (a b : CoefficientField m) :
    Commute (centralWord m 2 a) (centralWord m 4 b) := by
  rw [central_2, central_4]
  exact ((xc m 9 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).mul_right
    (xc m 9 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a (halfFrobenius m b))).mul_left
    ((xc m 8 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) b).mul_right
      (xc m 8 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m a) (halfFrobenius m b)))

theorem central_eighth (m : ℕ) (a u : CoefficientField m) :
    centralWord m 2 a * rootWord m 7 u =
      rootWord m 7 u * centralWord m 2 a * centralWord m 4 (a * u) := by
  rw [central_2, word_7, central_4, map_mul]
  have h₁ := xs m 9 22 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three])
    (by ext z; fin_cases z <;> norm_num [MatrixRelations.LongCommutators.V]) a u
  have h₂ := xs m 8 23 14 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three])
    (by ext z; fin_cases z <;> norm_num [MatrixRelations.LongCommutators.V])
    (halfFrobenius m a) (halfFrobenius m u)
  have hc (i j : Fin 24) (h : 0 ≤ dot (MatrixRelations.LongCommutators.V i)
      (MatrixRelations.LongCommutators.V j)) (s t : CoefficientField m) := xc m i j h s t
  simp only [mul_assoc]
  rw [(hc 8 22 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) _ _).left_comm, swap_suffix h₁]
  rw [(hc 15 8 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) _ _).left_comm]
  rw [(hc 15 23 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) _ _).eq]
  rw [swap_suffix h₂]
  rw [(hc 9 23 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) _ _).left_comm]
  rw [(hc 14 15 (by norm_num [MatrixRelations.LongCommutators.V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) _ _).eq]

end ReeF4.ReplacementCentralizerRoots
