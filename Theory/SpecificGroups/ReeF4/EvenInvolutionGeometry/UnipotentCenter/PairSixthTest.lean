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

private theorem c_6_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 10 b) :=
  xc m 6 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 11 b) :=
  xc m 6 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 14 b) :=
  xc m 6 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 15 b) :=
  xc m 6 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_6_16 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 16 b = X m 16 b * X m 6 a * X m 15 (a*b) :=
  xs m 6 16 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_6_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 17 b) :=
  xc m 6 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 20 b) :=
  xc m 6 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 21 b) :=
  xc m 6 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 10 b) :=
  xc m 7 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 11 b) :=
  xc m 7 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 14 b) :=
  xc m 7 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 15 b) :=
  xc m 7 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 16 b) :=
  xc m 7 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_7_17 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 17 b = X m 17 b * X m 7 a * X m 14 (a*b) :=
  xs m 7 17 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_7_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 20 b) :=
  xc m 7 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 21 b) :=
  xc m 7 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 6 b) :=
  xc m 8 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_7 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 7 b) :=
  xc m 8 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 10 b) :=
  xc m 8 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 11 b) :=
  xc m 8 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 14 b) :=
  xc m 8 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 15 b) :=
  xc m 8 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 16 b) :=
  xc m 8 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 17 b) :=
  xc m 8 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 20 b) :=
  xc m 8 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 21 b) :=
  xc m 8 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 6 b) :=
  xc m 9 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_7 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 7 b) :=
  xc m 9 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_8 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 8 b) :=
  xc m 9 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 10 b) :=
  xc m 14 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 11 b) :=
  xc m 14 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 10 b) :=
  xc m 15 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 11 b) :=
  xc m 15 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 14 b) :=
  xc m 15 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 17 b) :=
  xc m 15 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem left_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 6 1 * (X m 7 1 * (X m 8 1 * (1))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 1 * (X m 7 1 * (X m 8 (1 + (v 8)) * (X m 9 (v 9) * (1)))))))))))) := by
  rw [(c_9_6 m (v 9) 1).left_comm]
  rw [(c_8_6 m (v 8) 1).left_comm]
  rw [(c_9_7 m (v 9) 1).left_comm]
  rw [(c_8_7 m (v 8) 1).left_comm]
  rw [(c_9_8 m (v 9) 1).left_comm]
  rw [add_suffix m 8 (v 8) 1,
    show (v 8) + 1 = (1 + (v 8)) by ring]

private theorem collect_left (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 6 1 * (X m 7 1 * (X m 8 1 * (1))))))))))))) =
      splitWord m ![0, 0, 0, 0, 0, 0, 1, 1, (1 + (v 8)), (v 9), (v 10), (v 11), 0, 0, (v 14), (v 15), (v 16), (v 17), 0, 0, (v 20), (v 21), 0, 0] := by
  have h := (left_0 m v)
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

private theorem right_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 6 1 * (X m 7 1 * (X m 8 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 14 (v 17) * (X m 15 (v 16) * (X m 6 1 * (X m 11 (v 11) * (X m 7 1 * (X m 8 1 * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))) := by
  rw [(c_8_16 m 1 (v 16)).left_comm]
  rw [(c_7_16 m 1 (v 16)).left_comm]
  have h2 : X m 6 1 * X m 16 (v 16) = X m 16 (v 16) * X m 6 1 * X m 15 (v 16) := by
    have h := s_6_16 m 1 (v 16)
    rw [show 1 * (v 16) = (v 16) by ring] at h
    exact h
  rw [swap_suffix h2]
  rw [(c_6_15 m 1 (v 16)).left_comm]
  rw [(c_8_17 m 1 (v 17)).left_comm]
  have h5 : X m 7 1 * X m 17 (v 17) = X m 17 (v 17) * X m 7 1 * X m 14 (v 17) := by
    have h := s_7_17 m 1 (v 17)
    rw [show 1 * (v 17) = (v 17) by ring] at h
    exact h
  rw [swap_suffix h5]
  rw [(c_6_17 m 1 (v 17)).left_comm]
  rw [(c_15_17 m (v 16) (v 17)).left_comm]
  rw [(c_7_14 m 1 (v 17)).left_comm]
  rw [(c_6_14 m 1 (v 17)).left_comm]
  rw [(c_15_14 m (v 16) (v 17)).left_comm]
  rw [(c_8_10 m 1 (v 10)).left_comm]
  rw [(c_7_10 m 1 (v 10)).left_comm]
  rw [(c_6_10 m 1 (v 10)).left_comm]
  rw [(c_15_10 m (v 16) (v 10)).left_comm]
  rw [(c_14_10 m (v 17) (v 10)).left_comm]
  rw [(c_8_11 m 1 (v 11)).left_comm]
  rw [(c_7_11 m 1 (v 11)).left_comm]

private theorem right_1 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 14 (v 17) * (X m 15 (v 16) * (X m 6 1 * (X m 11 (v 11) * (X m 7 1 * (X m 8 1 * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 ((v 14) + (v 17)) * (X m 15 ((v 15) + (v 16)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 1 * (X m 7 1 * (X m 8 1 * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))) := by
  rw [(c_6_11 m 1 (v 11)).left_comm]
  rw [(c_15_11 m (v 16) (v 11)).left_comm]
  rw [(c_14_11 m (v 17) (v 11)).left_comm]
  rw [(c_8_14 m 1 (v 14)).left_comm]
  rw [(c_7_14 m 1 (v 14)).left_comm]
  rw [(c_6_14 m 1 (v 14)).left_comm]
  rw [(c_15_14 m (v 16) (v 14)).left_comm]
  rw [add_suffix m 14 (v 17) (v 14),
    show (v 17) + (v 14) = ((v 14) + (v 17)) by ring]
  rw [(c_8_15 m 1 (v 15)).left_comm]
  rw [(c_7_15 m 1 (v 15)).left_comm]
  rw [(c_6_15 m 1 (v 15)).left_comm]
  rw [add_suffix m 15 (v 16) (v 15),
    show (v 16) + (v 15) = ((v 15) + (v 16)) by ring]
  rw [(c_8_20 m 1 (v 20)).left_comm]
  rw [(c_7_20 m 1 (v 20)).left_comm]
  rw [(c_6_20 m 1 (v 20)).left_comm]
  rw [(c_8_21 m 1 (v 21)).left_comm]
  rw [(c_7_21 m 1 (v 21)).left_comm]
  rw [(c_6_21 m 1 (v 21)).left_comm]

private theorem right_2 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 ((v 14) + (v 17)) * (X m 15 ((v 15) + (v 16)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 1 * (X m 7 1 * (X m 8 1 * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 ((v 14) + (v 17)) * (X m 15 ((v 15) + (v 16)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 1 * (X m 7 1 * (X m 8 (1 + (v 8)) * (X m 9 (v 9) * (1)))))))))))) := by
  rw [add_suffix m 8 1 (v 8),
    show 1 + (v 8) = (1 + (v 8)) by ring]

private theorem collect_right (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 6 1 * (X m 7 1 * (X m 8 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))) =
      splitWord m ![0, 0, 0, 0, 0, 0, 1, 1, (1 + (v 8)), (v 9), (v 10), (v 11), 0, 0, ((v 14) + (v 17)), ((v 15) + (v 16)), (v 16), (v 17), 0, 0, (v 20), (v 21), 0, 0] := by
  have h := (right_0 m v).trans ((right_1 m v).trans ((right_2 m v)))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

/-- The indicated split coordinates vanish when the literal test word commutes. -/
theorem detect_pairsixth (m : ℕ) (v : Fin 24 → CoefficientField m)
    (hc : Commute (tailSplitWord m v) (rootWord m 2 1)) :
    v 16 = 0 := by
  have h : X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 6 1 * (X m 7 1 * (X m 8 1 * (1))))))))))))) = X m 6 1 * (X m 7 1 * (X m 8 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))) := by
    simpa only [tailSplitWord, word_2, map_one, one_mul, mul_one, xz, mul_assoc] using hc.eq
  have he := (collect_left m v).symm.trans (h.trans (collect_right m v))
  have hv := splitWord_injective m he
  have h := congrFun hv 15
  change (v 15) = ((v 15) + (v 16)) at h
  linear_combination -h

end ReeF4.EvenInvolutionGeometry.UnipotentCenter
