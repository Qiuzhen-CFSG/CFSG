module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords
/-!
# A central-root exchange for Ree involution conjugacy

The two equal-length split-root exchanges give
`y₃(e) x₈(t) = x₈(t) y₃(e) y₅(et)` in the actual split group.
The middle-tail conjugacy proof uses this to remove its y₅ coordinate.
Each adjacent exchange below is an instance of a checked F₄ matrix relation.
Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/
@[expose] public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open NormalizedRootCentralizers.CenterExponent.OuterElimination
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local irreducible] X

private theorem c_8_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 14 b) :=
  xc m 8 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 15 b) :=
  xc m 8 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 22 b) :=
  xc m 8 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_8_23 (m : ℕ) (a b : CoefficientField m) :
    X m 8 a * X m 23 b = X m 23 b * X m 8 a * X m 14 (a*b) :=
  xs m 8 23 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_9_8 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 8 b) :=
  xc m 9 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 14 b) :=
  xc m 9 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 15 b) :=
  xc m 9 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_9_22 (m : ℕ) (a b : CoefficientField m) :
    X m 9 a * X m 22 b = X m 22 b * X m 9 a * X m 15 (a*b) :=
  xs m 9 22 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_9_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 23 b) :=
  xc m 9 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 14 b) :=
  xc m 15 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 23 b) :=
  xc m 15 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem lhs (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 9 (v 0) * (X m 8 (v 1) * (X m 22 (v 2) * (X m 23 (v 3) * (1)))) =
      X m 22 (v 2) * (X m 23 (v 3) * (X m 14 ((v 1) * (v 3)) * (X m 15 ((v 0) * (v 2)) * (X m 8 (v 1) * (X m 9 (v 0) * (1)))))) := by
  rw [(c_9_8 m (v 0) (v 1)).left_comm]
  have h1 : X m 9 (v 0) * X m 22 (v 2) = X m 22 (v 2) * X m 9 (v 0) * X m 15 ((v 0) * (v 2)) := by
    have h := s_9_22 m (v 0) (v 2)
    rw [show (v 0) * (v 2) = ((v 0) * (v 2)) by ring] at h
    exact h
  rw [swap_suffix h1]
  rw [(c_8_22 m (v 1) (v 2)).left_comm]
  rw [(c_9_15 m (v 0) ((v 0) * (v 2))).left_comm]
  rw [(c_8_15 m (v 1) ((v 0) * (v 2))).left_comm]
  rw [(c_9_23 m (v 0) (v 3)).left_comm]
  have h6 : X m 8 (v 1) * X m 23 (v 3) = X m 23 (v 3) * X m 8 (v 1) * X m 14 ((v 1) * (v 3)) := by
    have h := s_8_23 m (v 1) (v 3)
    rw [show (v 1) * (v 3) = ((v 1) * (v 3)) by ring] at h
    exact h
  rw [swap_suffix h6]
  rw [(c_15_23 m ((v 0) * (v 2)) (v 3)).left_comm]
  rw [(c_8_14 m (v 1) ((v 1) * (v 3))).left_comm]
  rw [(c_15_14 m ((v 0) * (v 2)) ((v 1) * (v 3))).left_comm]

private theorem rhs (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 2) * (X m 23 (v 3) * (X m 9 (v 0) * (X m 8 (v 1) * (X m 15 ((v 0) * (v 2)) * (X m 14 ((v 1) * (v 3)) * (1)))))) =
      X m 22 (v 2) * (X m 23 (v 3) * (X m 14 ((v 1) * (v 3)) * (X m 15 ((v 0) * (v 2)) * (X m 8 (v 1) * (X m 9 (v 0) * (1)))))) := by
  rw [(c_9_8 m (v 0) (v 1)).left_comm]
  rw [(c_9_15 m (v 0) ((v 0) * (v 2))).left_comm]
  rw [(c_8_15 m (v 1) ((v 0) * (v 2))).left_comm]
  rw [(c_9_14 m (v 0) ((v 1) * (v 3))).left_comm]
  rw [(c_8_14 m (v 1) ((v 1) * (v 3))).left_comm]
  rw [(c_15_14 m ((v 0) * (v 2)) ((v 1) * (v 3))).left_comm]

private theorem swap_third_eighth (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 9 (v 0) * (X m 8 (v 1) * (X m 22 (v 2) * (X m 23 (v 3) * (1)))) =
      X m 22 (v 2) * (X m 23 (v 3) * (X m 9 (v 0) * (X m 8 (v 1) * (X m 15 ((v 0) * (v 2)) * (X m 14 ((v 1) * (v 3)) * (1)))))) := by
  exact (lhs m v).trans (rhs m v).symm
attribute [local semireducible] X

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong i), halfFrobenius]

/-- The literal exchange which removes the central fifth coordinate when
its central third companion is nonzero. -/
theorem central_third_eighth_swap (m : ℕ) (e t : CoefficientField m) :
    centralWord m 2 e * rootWord m 7 t =
      rootWord m 7 t * centralWord m 2 e * centralWord m 4 (e * t) := by
  have h := swap_third_eighth m ![e, halfFrobenius m e, t, halfFrobenius m t,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  have h2 : centralWord m 2 e = X m 9 e * X m 8 (halfFrobenius m e) := by
    simp only [centralWord, fieldEnd_half]
    rfl
  have h4 : centralWord m 4 (e * t) =
      X m 15 (e * t) * X m 14 (halfFrobenius m e * halfFrobenius m t) := by
    simp only [centralWord, fieldEnd_half, map_mul]
    rfl
  have h7 : rootWord m 7 t = X m 22 t * X m 23 (halfFrobenius m t) := by
    simp only [rootWord, fieldEnd_half]
    exact mul_one _
  rw [h2, h4, h7]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val, mul_one, mul_assoc] using h

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
