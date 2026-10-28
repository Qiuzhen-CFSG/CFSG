module
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter.TailWords
/-!
Checked split-root collection eliminating the remaining noncentral tail coordinates.
Each adjacent exchange is an instance of the actual split F₄ matrix relation;
the final coordinate comparison uses unique positive split coordinates.
Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/
public section
noncomputable section
namespace ReeF4.EvenInvolutionGeometry.UnipotentCenter
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open Theory.AlgebraicGroup.StandardRootSystem
open NormalizedRootCentralizers.CenterExponent.OuterElimination
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

private theorem c_9_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 15 b) :=
  xc m 9 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_9_22 (m : ℕ) (a b : CoefficientField m) :
    X m 9 a * X m 22 b = X m 22 b * X m 9 a * X m 15 (a*b) :=
  xs m 9 22 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_9_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 23 b) :=
  xc m 9 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_10_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 22 b) :=
  xc m 10 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_10_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 23 b) :=
  xc m 10 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 22 b) :=
  xc m 11 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 23 b) :=
  xc m 11 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 22 b) :=
  xc m 14 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 23 b) :=
  xc m 14 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 14 b) :=
  xc m 15 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 22 b) :=
  xc m 15 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 23 b) :=
  xc m 15 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_16_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 16 a) (X m 22 b) :=
  xc m 16 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_16_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 16 a) (X m 23 b) :=
  xc m 16 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 22 b) :=
  xc m 17 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 23 b) :=
  xc m 17 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 14 b) :=
  xc m 20 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 15 b) :=
  xc m 20 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 22 b) :=
  xc m 20 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 23 b) :=
  xc m 20 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 14 b) :=
  xc m 21 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 15 b) :=
  xc m 21 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 22 b) :=
  xc m 21 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 23 b) :=
  xc m 21 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem left_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 22 1 * (X m 23 1 * (1)))))))))))) =
      X m 22 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 ((v 15) + (v 9)) * (X m 20 (v 20) * (X m 23 1 * (X m 21 (v 21) * (X m 8 (v 8) * (X m 14 (v 8) * (X m 9 (v 9) * (1))))))))))))) := by
  have h0 : X m 9 (v 9) * X m 22 1 = X m 22 1 * X m 9 (v 9) * X m 15 (v 9) := by
    have h := s_9_22 m (v 9) 1
    rw [show (v 9) * 1 = (v 9) by ring] at h
    exact h
  rw [swap_suffix h0]
  rw [(c_8_22 m (v 8) 1).left_comm]
  rw [(c_21_22 m (v 21) 1).left_comm]
  rw [(c_20_22 m (v 20) 1).left_comm]
  rw [(c_15_22 m (v 15) 1).left_comm]
  rw [(c_14_22 m (v 14) 1).left_comm]
  rw [(c_11_22 m (v 11) 1).left_comm]
  rw [(c_10_22 m (v 10) 1).left_comm]
  rw [(c_17_22 m (v 17) 1).left_comm]
  rw [(c_16_22 m (v 16) 1).left_comm]
  rw [(c_9_15 m (v 9) (v 9)).left_comm]
  rw [(c_8_15 m (v 8) (v 9)).left_comm]
  rw [(c_21_15 m (v 21) (v 9)).left_comm]
  rw [(c_20_15 m (v 20) (v 9)).left_comm]
  rw [add_suffix m 15 (v 15) (v 9),
    show (v 15) + (v 9) = ((v 15) + (v 9)) by ring]
  rw [(c_9_23 m (v 9) 1).left_comm]
  have h16 : X m 8 (v 8) * X m 23 1 = X m 23 1 * X m 8 (v 8) * X m 14 (v 8) := by
    have h := s_8_23 m (v 8) 1
    rw [show (v 8) * 1 = (v 8) by ring] at h
    exact h
  rw [swap_suffix h16]
  rw [(c_21_23 m (v 21) 1).left_comm]

private theorem left_1 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 ((v 15) + (v 9)) * (X m 20 (v 20) * (X m 23 1 * (X m 21 (v 21) * (X m 8 (v 8) * (X m 14 (v 8) * (X m 9 (v 9) * (1))))))))))))) =
      X m 22 1 * (X m 23 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 ((v 14) + (v 8)) * (X m 15 ((v 15) + (v 9)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))) := by
  rw [(c_20_23 m (v 20) 1).left_comm]
  rw [(c_15_23 m ((v 15) + (v 9)) 1).left_comm]
  rw [(c_14_23 m (v 14) 1).left_comm]
  rw [(c_11_23 m (v 11) 1).left_comm]
  rw [(c_10_23 m (v 10) 1).left_comm]
  rw [(c_17_23 m (v 17) 1).left_comm]
  rw [(c_16_23 m (v 16) 1).left_comm]
  rw [(c_8_14 m (v 8) (v 8)).left_comm]
  rw [(c_21_14 m (v 21) (v 8)).left_comm]
  rw [(c_20_14 m (v 20) (v 8)).left_comm]
  rw [(c_15_14 m ((v 15) + (v 9)) (v 8)).left_comm]
  rw [add_suffix m 14 (v 14) (v 8),
    show (v 14) + (v 8) = ((v 14) + (v 8)) by ring]

private theorem collect_left (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 22 1 * (X m 23 1 * (1)))))))))))) =
      splitWord m ![0, 0, 0, 0, 0, 0, 0, 0, (v 8), (v 9), (v 10), (v 11), 0, 0, ((v 14) + (v 8)), ((v 15) + (v 9)), (v 16), (v 17), 0, 0, (v 20), (v 21), 1, 1] := by
  have h := (left_0 m v).trans ((left_1 m v))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

private theorem collect_right (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 1 * (X m 23 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))) =
      splitWord m ![0, 0, 0, 0, 0, 0, 0, 0, (v 8), (v 9), (v 10), (v 11), 0, 0, (v 14), (v 15), (v 16), (v 17), 0, 0, (v 20), (v 21), 1, 1] := by
  simp only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, xz, one_mul]

/-- The indicated split coordinates vanish when the literal test word commutes. -/
theorem detect_centralthird (m : ℕ) (v : Fin 24 → CoefficientField m)
    (hc : Commute (tailSplitWord m v) (rootWord m 7 1)) :
    v 9 = 0 := by
  have h : X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 22 1 * (X m 23 1 * (1)))))))))))) = X m 22 1 * (X m 23 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))) := by
    simpa only [tailSplitWord, word_7, map_one, one_mul, mul_one, xz, mul_assoc] using hc.eq
  have he := (collect_left m v).symm.trans (h.trans (collect_right m v))
  have hv := splitWord_injective m he
  have h := congrFun hv 15
  change ((v 15) + (v 9)) = (v 15) at h
  linear_combination h

end ReeF4.EvenInvolutionGeometry.UnipotentCenter
