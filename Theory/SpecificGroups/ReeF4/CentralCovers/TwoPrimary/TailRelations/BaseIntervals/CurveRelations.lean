module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations.Geometry
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations.BaseIntervals.ShortExchanges
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.ShortCommutators
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators

/-!
# Angular interval bounds for the main Ree root curves

The fourteen nontrivial exchanges and fourteen commuting pairs imply that
the source right commutator of two main curves lies in any subgroup containing
the intervening whole root blocks. In particular the central curves in B₂
blocks are retained via their proved containment in X. This generator-level
statement will be extended to normalization of the generated angular tails.

Source: GLS3, 2.4.5(d) and Corollary 2.4.6,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
open Theory.AlgebraicGroup StandardRootSystem
namespace ReeF4.CentralCovers.TwoPrimary.TailRelations.BaseIntervals
open Subgroup ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics MatrixRelations MatrixRelations.LongCommutators
open Parabolics.RadicalCoordinates.FixedCoordinates
noncomputable section
private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (longRoot_isLong i), halfFrobenius]

private theorem word_0 (m : ℕ) (t : CoefficientField m) :
    rootWord m 0 t = MatrixRelations.LongCommutators.X m 0 t * MatrixRelations.LongCommutators.X m 1 (halfFrobenius m t) * MatrixRelations.LongCommutators.X m 2 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_1 (m : ℕ) (t : CoefficientField m) :
    rootWord m 1 t = MatrixRelations.LongCommutators.X m 4 t * MatrixRelations.LongCommutators.X m 5 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change MatrixRelations.LongCommutators.X m 4 t * MatrixRelations.LongCommutators.X m 5 (halfFrobenius m t) * 1 = _
  exact mul_one _

private theorem word_2 (m : ℕ) (t : CoefficientField m) :
    rootWord m 2 t = MatrixRelations.LongCommutators.X m 6 t * MatrixRelations.LongCommutators.X m 7 (halfFrobenius m t) * MatrixRelations.LongCommutators.X m 8 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_3 (m : ℕ) (t : CoefficientField m) :
    rootWord m 3 t = MatrixRelations.LongCommutators.X m 10 t * MatrixRelations.LongCommutators.X m 11 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change MatrixRelations.LongCommutators.X m 10 t * MatrixRelations.LongCommutators.X m 11 (halfFrobenius m t) * 1 = _
  exact mul_one _

private theorem word_4 (m : ℕ) (t : CoefficientField m) :
    rootWord m 4 t = MatrixRelations.LongCommutators.X m 12 t * MatrixRelations.LongCommutators.X m 13 (halfFrobenius m t) * MatrixRelations.LongCommutators.X m 14 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_5 (m : ℕ) (t : CoefficientField m) :
    rootWord m 5 t = MatrixRelations.LongCommutators.X m 16 t * MatrixRelations.LongCommutators.X m 17 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change MatrixRelations.LongCommutators.X m 16 t * MatrixRelations.LongCommutators.X m 17 (halfFrobenius m t) * 1 = _
  exact mul_one _

private theorem word_6 (m : ℕ) (t : CoefficientField m) :
    rootWord m 6 t = MatrixRelations.LongCommutators.X m 18 t * MatrixRelations.LongCommutators.X m 19 (halfFrobenius m t) * MatrixRelations.LongCommutators.X m 20 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_7 (m : ℕ) (t : CoefficientField m) :
    rootWord m 7 t = MatrixRelations.LongCommutators.X m 22 t * MatrixRelations.LongCommutators.X m 23 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change MatrixRelations.LongCommutators.X m 22 t * MatrixRelations.LongCommutators.X m 23 (halfFrobenius m t) * 1 = _
  exact mul_one _

private theorem commute_0_1 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 0 t) (rootWord m 1 u) := by
  rw [word_0, word_1]
  exact ((((xc m 0 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 0 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_left ((xc m 1 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 1 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u)))).mul_left ((xc m 2 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (u)).mul_right (xc m 2 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (halfFrobenius m u))))

private theorem commute_0_4 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 0 t) (rootWord m 4 u) := by
  rw [word_0, word_4]
  exact (((((xc m 0 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 0 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_right (xc m 0 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u * halfFrobenius m u))).mul_left (((xc m 1 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 1 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u))).mul_right (xc m 1 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u * halfFrobenius m u)))).mul_left (((xc m 2 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (u)).mul_right (xc m 2 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (halfFrobenius m u))).mul_right (xc m 2 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (u * halfFrobenius m u))))

private theorem commute_1_2 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 1 t) (rootWord m 2 u) := by
  rw [word_1, word_2]
  exact ((((xc m 4 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 4 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_right (xc m 4 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u * halfFrobenius m u))).mul_left (((xc m 5 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 5 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u))).mul_right (xc m 5 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u * halfFrobenius m u))))

private theorem commute_1_3 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 1 t) (rootWord m 3 u) := by
  rw [word_1, word_3]
  exact (((xc m 4 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 4 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_left ((xc m 5 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 5 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u))))

private theorem commute_1_5 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 1 t) (rootWord m 5 u) := by
  rw [word_1, word_5]
  exact (((xc m 4 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 4 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_left ((xc m 5 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 5 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u))))

private theorem commute_2_3 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 2 t) (rootWord m 3 u) := by
  rw [word_2, word_3]
  exact ((((xc m 6 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 6 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_left ((xc m 7 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 7 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u)))).mul_left ((xc m 8 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (u)).mul_right (xc m 8 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (halfFrobenius m u))))

private theorem commute_2_6 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 2 t) (rootWord m 6 u) := by
  rw [word_2, word_6]
  exact (((((xc m 6 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 6 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_right (xc m 6 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u * halfFrobenius m u))).mul_left (((xc m 7 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 7 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u))).mul_right (xc m 7 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u * halfFrobenius m u)))).mul_left (((xc m 8 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (u)).mul_right (xc m 8 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (halfFrobenius m u))).mul_right (xc m 8 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (u * halfFrobenius m u))))

private theorem commute_3_4 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 3 t) (rootWord m 4 u) := by
  rw [word_3, word_4]
  exact ((((xc m 10 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 10 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_right (xc m 10 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u * halfFrobenius m u))).mul_left (((xc m 11 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 11 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u))).mul_right (xc m 11 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u * halfFrobenius m u))))

private theorem commute_3_5 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 3 t) (rootWord m 5 u) := by
  rw [word_3, word_5]
  exact (((xc m 10 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 10 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_left ((xc m 11 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 11 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u))))

private theorem commute_3_7 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 3 t) (rootWord m 7 u) := by
  rw [word_3, word_7]
  exact (((xc m 10 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 10 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_left ((xc m 11 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 11 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u))))

private theorem commute_4_5 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 4 t) (rootWord m 5 u) := by
  rw [word_4, word_5]
  exact ((((xc m 12 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 12 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_left ((xc m 13 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 13 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u)))).mul_left ((xc m 14 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (u)).mul_right (xc m 14 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (halfFrobenius m u))))

private theorem commute_5_6 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 5 t) (rootWord m 6 u) := by
  rw [word_5, word_6]
  exact ((((xc m 16 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 16 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_right (xc m 16 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u * halfFrobenius m u))).mul_left (((xc m 17 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 17 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u))).mul_right (xc m 17 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u * halfFrobenius m u))))

private theorem commute_5_7 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 5 t) (rootWord m 7 u) := by
  rw [word_5, word_7]
  exact (((xc m 16 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 16 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_left ((xc m 17 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 17 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u))))

private theorem commute_6_7 (m : ℕ) (t u : CoefficientField m) :
    Commute (rootWord m 6 t) (rootWord m 7 u) := by
  rw [word_6, word_7]
  exact ((((xc m 18 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (u)).mul_right (xc m 18 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t) (halfFrobenius m u))).mul_left ((xc m 19 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (u)).mul_right (xc m 19 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (halfFrobenius m t) (halfFrobenius m u)))).mul_left ((xc m 20 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (u)).mul_right (xc m 20 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (t * halfFrobenius m t) (halfFrobenius m u))))

/-- Generator form of the source angular-interval law in the literal fixed group. -/
theorem main_commutator_mem (m : ℕ) (i j : Fin 8) (hij : i < j)
    (H : Subgroup (Model m))
    (hH : ∀ k : Fin 8, i < k → k < j → ElementaryTwoBound.X m k ≤ H)
    (t u : CoefficientField m) :
    (mainElement m i t)⁻¹ * (mainElement m j u)⁻¹ *
      mainElement m i t * mainElement m j u ∈ H := by
  have hm (k : Fin 8) (hk : i < k) (hkj : k < j) (a : CoefficientField m) :
      mainElement m k a ∈ H := hH k hk hkj (mainElement_mem_X m k a)
  have hy (k : Fin 8) (hk : i < k) (hkj : k < j)
      (he : k.val % 2 = 0) (a : CoefficientField m) :
      centralElement m k a ∈ H :=
    hH k hk hkj (Y_le_X m k he (centralElement_mem_Y m k a))
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · change (mainElement m 0 t)⁻¹ * (mainElement m 1 u)⁻¹ *
        mainElement m 0 t * mainElement m 1 u ∈ H
    have hc : Commute (mainElement m 0 t) (mainElement m 1 u) :=
      Subtype.ext (commute_0_1 m t u).eq
    have he : (mainElement m 0 t)⁻¹ * (mainElement m 1 u)⁻¹ *
        mainElement m 0 t * mainElement m 1 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 0 t)⁻¹ * (mainElement m 2 u)⁻¹ *
        mainElement m 0 t * mainElement m 2 u ∈ H
    have he : (mainElement m 0 t)⁻¹ * (mainElement m 2 u)⁻¹ *
        mainElement m 0 t * mainElement m 2 u =
        mainElement m 1 (t * u) := Subtype.ext (rootWord_commutator_0_2 m t u)
    rw [he]
    exact (hm 1 (by decide) (by decide) _)
  · change (mainElement m 0 t)⁻¹ * (mainElement m 3 u)⁻¹ *
        mainElement m 0 t * mainElement m 3 u ∈ H
    have he : (mainElement m 0 t)⁻¹ * (mainElement m 3 u)⁻¹ *
        mainElement m 0 t * mainElement m 3 u =
        centralElement m 2 (t * u) := Subtype.ext (rootWord_first_fourth_commutator m t u)
    rw [he]
    exact (hy 2 (by decide) (by decide) (by decide) _)
  · change (mainElement m 0 t)⁻¹ * (mainElement m 4 u)⁻¹ *
        mainElement m 0 t * mainElement m 4 u ∈ H
    have hc : Commute (mainElement m 0 t) (mainElement m 4 u) :=
      Subtype.ext (commute_0_4 m t u).eq
    have he : (mainElement m 0 t)⁻¹ * (mainElement m 4 u)⁻¹ *
        mainElement m 0 t * mainElement m 4 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 0 t)⁻¹ * (mainElement m 5 u)⁻¹ *
        mainElement m 0 t * mainElement m 5 u ∈ H
    have he : (mainElement m 0 t)⁻¹ * (mainElement m 5 u)⁻¹ *
        mainElement m 0 t * mainElement m 5 u =
        mainElement m 3 (titsEnd m t * u) * centralElement m 4 (t * titsEnd m u) := Subtype.ext (rootWord_first_sixth_commutator m t u)
    rw [he]
    exact (H.mul_mem (hm 3 (by decide) (by decide) _) (hy 4 (by decide) (by decide) (by decide) _))
  · change (mainElement m 0 t)⁻¹ * (mainElement m 6 u)⁻¹ *
        mainElement m 0 t * mainElement m 6 u ∈ H
    have he : (mainElement m 0 t)⁻¹ * (mainElement m 6 u)⁻¹ *
        mainElement m 0 t * mainElement m 6 u =
        (mainElement m 2 (titsEnd m t * u))⁻¹ * mainElement m 3 ((t * titsEnd m t) * (u * titsEnd m u)) * mainElement m 4 (t * titsEnd m u) := Subtype.ext (rootWord_first_seventh_commutator m t u)
    rw [he]
    exact (H.mul_mem (H.mul_mem (H.inv_mem (hm 2 (by decide) (by decide) _)) (hm 3 (by decide) (by decide) _)) (hm 4 (by decide) (by decide) _))
  · change (mainElement m 0 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 0 t * mainElement m 7 u ∈ H
    have he : (mainElement m 0 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 0 t * mainElement m 7 u =
        mainElement m 1 ((t ^ 2 * titsEnd m t) * u) * (mainElement m 2 ((t * titsEnd m t) * u))⁻¹ * mainElement m 3 ((t ^ 2 * titsEnd m t ^ 2) * (u * titsEnd m u)) * centralElement m 4 ((t ^ 3 * titsEnd m t ^ 2) * (u ^ 2 * titsEnd m u)) * mainElement m 5 ((t ^ 2 * titsEnd m t) * (u * titsEnd m u)) * mainElement m 6 (t * u) := Subtype.ext (rootWord_first_eighth_commutator m t u)
    rw [he]
    exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hm 1 (by decide) (by decide) _) (H.inv_mem (hm 2 (by decide) (by decide) _))) (hm 3 (by decide) (by decide) _)) (hy 4 (by decide) (by decide) (by decide) _)) (hm 5 (by decide) (by decide) _)) (hm 6 (by decide) (by decide) _))
  · change (mainElement m 1 t)⁻¹ * (mainElement m 2 u)⁻¹ *
        mainElement m 1 t * mainElement m 2 u ∈ H
    have hc : Commute (mainElement m 1 t) (mainElement m 2 u) :=
      Subtype.ext (commute_1_2 m t u).eq
    have he : (mainElement m 1 t)⁻¹ * (mainElement m 2 u)⁻¹ *
        mainElement m 1 t * mainElement m 2 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 1 t)⁻¹ * (mainElement m 3 u)⁻¹ *
        mainElement m 1 t * mainElement m 3 u ∈ H
    have hc : Commute (mainElement m 1 t) (mainElement m 3 u) :=
      Subtype.ext (commute_1_3 m t u).eq
    have he : (mainElement m 1 t)⁻¹ * (mainElement m 3 u)⁻¹ *
        mainElement m 1 t * mainElement m 3 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 1 t)⁻¹ * (mainElement m 4 u)⁻¹ *
        mainElement m 1 t * mainElement m 4 u ∈ H
    have he : (mainElement m 1 t)⁻¹ * (mainElement m 4 u)⁻¹ *
        mainElement m 1 t * mainElement m 4 u =
        centralElement m 2 (t * u) := Subtype.ext (rootWord_commutator_1_4 m t u)
    rw [he]
    exact (hy 2 (by decide) (by decide) (by decide) _)
  · change (mainElement m 1 t)⁻¹ * (mainElement m 5 u)⁻¹ *
        mainElement m 1 t * mainElement m 5 u ∈ H
    have hc : Commute (mainElement m 1 t) (mainElement m 5 u) :=
      Subtype.ext (commute_1_5 m t u).eq
    have he : (mainElement m 1 t)⁻¹ * (mainElement m 5 u)⁻¹ *
        mainElement m 1 t * mainElement m 5 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 1 t)⁻¹ * (mainElement m 6 u)⁻¹ *
        mainElement m 1 t * mainElement m 6 u ∈ H
    have he : (mainElement m 1 t)⁻¹ * (mainElement m 6 u)⁻¹ *
        mainElement m 1 t * mainElement m 6 u =
        mainElement m 3 (t * titsEnd m u) * centralElement m 2 (titsEnd m t * u) := Subtype.ext (rootWord_commutator_1_6 m t u)
    rw [he]
    exact (H.mul_mem (hm 3 (by decide) (by decide) _) (hy 2 (by decide) (by decide) (by decide) _))
  · change (mainElement m 1 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 1 t * mainElement m 7 u ∈ H
    have he : (mainElement m 1 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 1 t * mainElement m 7 u =
        mainElement m 3 (titsEnd m t * u) * mainElement m 5 (t * titsEnd m u) := Subtype.ext (rootWord_second_eighth_commutator m t u)
    rw [he]
    exact (H.mul_mem (hm 3 (by decide) (by decide) _) (hm 5 (by decide) (by decide) _))
  · change (mainElement m 2 t)⁻¹ * (mainElement m 3 u)⁻¹ *
        mainElement m 2 t * mainElement m 3 u ∈ H
    have hc : Commute (mainElement m 2 t) (mainElement m 3 u) :=
      Subtype.ext (commute_2_3 m t u).eq
    have he : (mainElement m 2 t)⁻¹ * (mainElement m 3 u)⁻¹ *
        mainElement m 2 t * mainElement m 3 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 2 t)⁻¹ * (mainElement m 4 u)⁻¹ *
        mainElement m 2 t * mainElement m 4 u ∈ H
    have he : (mainElement m 2 t)⁻¹ * (mainElement m 4 u)⁻¹ *
        mainElement m 2 t * mainElement m 4 u =
        mainElement m 3 (t * u) := Subtype.ext (rootWord_commutator_2_4 m t u)
    rw [he]
    exact (hm 3 (by decide) (by decide) _)
  · change (mainElement m 2 t)⁻¹ * (mainElement m 5 u)⁻¹ *
        mainElement m 2 t * mainElement m 5 u ∈ H
    have he : (mainElement m 2 t)⁻¹ * (mainElement m 5 u)⁻¹ *
        mainElement m 2 t * mainElement m 5 u =
        centralElement m 4 (t * u) := Subtype.ext (rootWord_commutator_2_5 m t u)
    rw [he]
    exact (hy 4 (by decide) (by decide) (by decide) _)
  · change (mainElement m 2 t)⁻¹ * (mainElement m 6 u)⁻¹ *
        mainElement m 2 t * mainElement m 6 u ∈ H
    have hc : Commute (mainElement m 2 t) (mainElement m 6 u) :=
      Subtype.ext (commute_2_6 m t u).eq
    have he : (mainElement m 2 t)⁻¹ * (mainElement m 6 u)⁻¹ *
        mainElement m 2 t * mainElement m 6 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 2 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 2 t * mainElement m 7 u ∈ H
    have he : (mainElement m 2 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 2 t * mainElement m 7 u =
        mainElement m 5 (titsEnd m t * u) * centralElement m 6 (t * titsEnd m u) := Subtype.ext (rootWord_commutator_2_7 m t u)
    rw [he]
    exact (H.mul_mem (hm 5 (by decide) (by decide) _) (hy 6 (by decide) (by decide) (by decide) _))
  · change (mainElement m 3 t)⁻¹ * (mainElement m 4 u)⁻¹ *
        mainElement m 3 t * mainElement m 4 u ∈ H
    have hc : Commute (mainElement m 3 t) (mainElement m 4 u) :=
      Subtype.ext (commute_3_4 m t u).eq
    have he : (mainElement m 3 t)⁻¹ * (mainElement m 4 u)⁻¹ *
        mainElement m 3 t * mainElement m 4 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 3 t)⁻¹ * (mainElement m 5 u)⁻¹ *
        mainElement m 3 t * mainElement m 5 u ∈ H
    have hc : Commute (mainElement m 3 t) (mainElement m 5 u) :=
      Subtype.ext (commute_3_5 m t u).eq
    have he : (mainElement m 3 t)⁻¹ * (mainElement m 5 u)⁻¹ *
        mainElement m 3 t * mainElement m 5 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 3 t)⁻¹ * (mainElement m 6 u)⁻¹ *
        mainElement m 3 t * mainElement m 6 u ∈ H
    have he : (mainElement m 3 t)⁻¹ * (mainElement m 6 u)⁻¹ *
        mainElement m 3 t * mainElement m 6 u =
        centralElement m 4 (t * u) := Subtype.ext (rootWord_commutator_3_6 m t u)
    rw [he]
    exact (hy 4 (by decide) (by decide) (by decide) _)
  · change (mainElement m 3 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 3 t * mainElement m 7 u ∈ H
    have hc : Commute (mainElement m 3 t) (mainElement m 7 u) :=
      Subtype.ext (commute_3_7 m t u).eq
    have he : (mainElement m 3 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 3 t * mainElement m 7 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 4 t)⁻¹ * (mainElement m 5 u)⁻¹ *
        mainElement m 4 t * mainElement m 5 u ∈ H
    have hc : Commute (mainElement m 4 t) (mainElement m 5 u) :=
      Subtype.ext (commute_4_5 m t u).eq
    have he : (mainElement m 4 t)⁻¹ * (mainElement m 5 u)⁻¹ *
        mainElement m 4 t * mainElement m 5 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 4 t)⁻¹ * (mainElement m 6 u)⁻¹ *
        mainElement m 4 t * mainElement m 6 u ∈ H
    have he : (mainElement m 4 t)⁻¹ * (mainElement m 6 u)⁻¹ *
        mainElement m 4 t * mainElement m 6 u =
        mainElement m 5 (t * u) := Subtype.ext (rootWord_commutator_4_6 m t u)
    rw [he]
    exact (hm 5 (by decide) (by decide) _)
  · change (mainElement m 4 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 4 t * mainElement m 7 u ∈ H
    have he : (mainElement m 4 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 4 t * mainElement m 7 u =
        centralElement m 6 (t * u) := Subtype.ext (rootWord_commutator_4_7 m t u)
    rw [he]
    exact (hy 6 (by decide) (by decide) (by decide) _)
  · change (mainElement m 5 t)⁻¹ * (mainElement m 6 u)⁻¹ *
        mainElement m 5 t * mainElement m 6 u ∈ H
    have hc : Commute (mainElement m 5 t) (mainElement m 6 u) :=
      Subtype.ext (commute_5_6 m t u).eq
    have he : (mainElement m 5 t)⁻¹ * (mainElement m 6 u)⁻¹ *
        mainElement m 5 t * mainElement m 6 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 5 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 5 t * mainElement m 7 u ∈ H
    have hc : Commute (mainElement m 5 t) (mainElement m 7 u) :=
      Subtype.ext (commute_5_7 m t u).eq
    have he : (mainElement m 5 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 5 t * mainElement m 7 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem
  · change (mainElement m 6 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 6 t * mainElement m 7 u ∈ H
    have hc : Commute (mainElement m 6 t) (mainElement m 7 u) :=
      Subtype.ext (commute_6_7 m t u).eq
    have he : (mainElement m 6 t)⁻¹ * (mainElement m 7 u)⁻¹ *
        mainElement m 6 t * mainElement m 7 u = 1 := by
      rw [mul_assoc, mul_assoc, hc.eq, inv_mul_cancel_left, inv_mul_cancel]
    rw [he]
    exact H.one_mem

end
end ReeF4.CentralCovers.TwoPrimary.TailRelations.BaseIntervals
