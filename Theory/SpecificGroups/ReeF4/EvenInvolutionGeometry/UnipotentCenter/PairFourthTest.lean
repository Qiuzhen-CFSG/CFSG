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

private theorem c_8_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 18 b) :=
  xc m 8 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 19 b) :=
  xc m 8 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 20 b) :=
  xc m 8 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 18 b) :=
  xc m 9 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 19 b) :=
  xc m 9 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 20 b) :=
  xc m 9 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 11 b) :=
  xc m 15 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 14 b) :=
  xc m 15 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_18_10 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 10 b = X m 10 b * X m 18 a * X m 15 (a*b) :=
  xs m 18 10 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_18_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 11 b) :=
  xc m 18 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_18_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 14 b) :=
  xc m 18 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_18_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 15 b) :=
  xc m 18 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_18_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 16 b) :=
  xc m 18 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_18_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 17 b) :=
  xc m 18 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 10 b) :=
  xc m 19 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_19_11 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 11 b = X m 11 b * X m 19 a * X m 14 (a*b) :=
  xs m 19 11 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_19_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 14 b) :=
  xc m 19 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 15 b) :=
  xc m 19 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 16 b) :=
  xc m 19 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 17 b) :=
  xc m 19 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 10 b) :=
  xc m 20 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 11 b) :=
  xc m 20 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 14 b) :=
  xc m 20 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 15 b) :=
  xc m 20 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 16 b) :=
  xc m 20 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 17 b) :=
  xc m 20 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 18 b) :=
  xc m 20 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 19 b) :=
  xc m 20 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 18 b) :=
  xc m 21 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 19 b) :=
  xc m 21 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 20 b) :=
  xc m 21 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem left_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (1))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 1 * (X m 19 1 * (X m 20 (1 + (v 20)) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))) := by
  rw [(c_9_18 m (v 9) 1).left_comm]
  rw [(c_8_18 m (v 8) 1).left_comm]
  rw [(c_21_18 m (v 21) 1).left_comm]
  rw [(c_20_18 m (v 20) 1).left_comm]
  rw [(c_9_19 m (v 9) 1).left_comm]
  rw [(c_8_19 m (v 8) 1).left_comm]
  rw [(c_21_19 m (v 21) 1).left_comm]
  rw [(c_20_19 m (v 20) 1).left_comm]
  rw [(c_9_20 m (v 9) 1).left_comm]
  rw [(c_8_20 m (v 8) 1).left_comm]
  rw [(c_21_20 m (v 21) 1).left_comm]
  rw [add_suffix m 20 (v 20) 1,
    show (v 20) + 1 = (1 + (v 20)) by ring]

private theorem collect_left (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (1))))))))))))) =
      splitWord m ![0, 0, 0, 0, 0, 0, 0, 0, (v 8), (v 9), (v 10), (v 11), 0, 0, (v 14), (v 15), (v 16), (v 17), 1, 1, (1 + (v 20)), (v 21), 0, 0] := by
  have h := (left_0 m v)
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

private theorem right_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 11) * (X m 15 (v 10) * (X m 18 1 * (X m 19 1 * (X m 14 (v 14) * (X m 20 1 * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))) := by
  rw [(c_20_16 m 1 (v 16)).left_comm]
  rw [(c_19_16 m 1 (v 16)).left_comm]
  rw [(c_18_16 m 1 (v 16)).left_comm]
  rw [(c_20_17 m 1 (v 17)).left_comm]
  rw [(c_19_17 m 1 (v 17)).left_comm]
  rw [(c_18_17 m 1 (v 17)).left_comm]
  rw [(c_20_10 m 1 (v 10)).left_comm]
  rw [(c_19_10 m 1 (v 10)).left_comm]
  have h8 : X m 18 1 * X m 10 (v 10) = X m 10 (v 10) * X m 18 1 * X m 15 (v 10) := by
    have h := s_18_10 m 1 (v 10)
    rw [show 1 * (v 10) = (v 10) by ring] at h
    exact h
  rw [swap_suffix h8]
  rw [(c_18_15 m 1 (v 10)).left_comm]
  rw [(c_20_11 m 1 (v 11)).left_comm]
  have h11 : X m 19 1 * X m 11 (v 11) = X m 11 (v 11) * X m 19 1 * X m 14 (v 11) := by
    have h := s_19_11 m 1 (v 11)
    rw [show 1 * (v 11) = (v 11) by ring] at h
    exact h
  rw [swap_suffix h11]
  rw [(c_18_11 m 1 (v 11)).left_comm]
  rw [(c_15_11 m (v 10) (v 11)).left_comm]
  rw [(c_19_14 m 1 (v 11)).left_comm]
  rw [(c_18_14 m 1 (v 11)).left_comm]
  rw [(c_15_14 m (v 10) (v 11)).left_comm]
  rw [(c_20_14 m 1 (v 14)).left_comm]

private theorem right_1 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 11) * (X m 15 (v 10) * (X m 18 1 * (X m 19 1 * (X m 14 (v 14) * (X m 20 1 * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 ((v 11) + (v 14)) * (X m 15 ((v 10) + (v 15)) * (X m 18 1 * (X m 19 1 * (X m 20 (1 + (v 20)) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))) := by
  rw [(c_19_14 m 1 (v 14)).left_comm]
  rw [(c_18_14 m 1 (v 14)).left_comm]
  rw [(c_15_14 m (v 10) (v 14)).left_comm]
  rw [add_suffix m 14 (v 11) (v 14),
    show (v 11) + (v 14) = ((v 11) + (v 14)) by ring]
  rw [(c_20_15 m 1 (v 15)).left_comm]
  rw [(c_19_15 m 1 (v 15)).left_comm]
  rw [(c_18_15 m 1 (v 15)).left_comm]
  rw [add_suffix m 15 (v 10) (v 15),
    show (v 10) + (v 15) = ((v 10) + (v 15)) by ring]
  rw [add_suffix m 20 1 (v 20),
    show 1 + (v 20) = (1 + (v 20)) by ring]

private theorem collect_right (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))) =
      splitWord m ![0, 0, 0, 0, 0, 0, 0, 0, (v 8), (v 9), (v 10), (v 11), 0, 0, ((v 11) + (v 14)), ((v 10) + (v 15)), (v 16), (v 17), 1, 1, (1 + (v 20)), (v 21), 0, 0] := by
  have h := (right_0 m v).trans ((right_1 m v))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

/-- The indicated split coordinates vanish when the literal test word commutes. -/
theorem detect_pairfourth (m : ℕ) (v : Fin 24 → CoefficientField m)
    (hc : Commute (tailSplitWord m v) (rootWord m 6 1)) :
    v 10 = 0 := by
  have h : X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (1))))))))))))) = X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))) := by
    simpa only [tailSplitWord, word_6, map_one, one_mul, mul_one, xz, mul_assoc] using hc.eq
  have he := (collect_left m v).symm.trans (h.trans (collect_right m v))
  have hv := splitWord_injective m he
  have h := congrFun hv 15
  change (v 15) = ((v 10) + (v 15)) at h
  linear_combination -h

end ReeF4.EvenInvolutionGeometry.UnipotentCenter
