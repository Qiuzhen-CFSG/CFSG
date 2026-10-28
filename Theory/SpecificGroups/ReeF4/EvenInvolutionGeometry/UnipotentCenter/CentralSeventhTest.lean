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

private theorem c_8_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 4 b) :=
  xc m 8 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 5 b) :=
  xc m 8 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 4 b) :=
  xc m 9 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 5 b) :=
  xc m 9 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_10_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 4 b) :=
  xc m 10 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_10_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 5 b) :=
  xc m 10 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 4 b) :=
  xc m 11 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 5 b) :=
  xc m 11 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 4 b) :=
  xc m 14 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 5 b) :=
  xc m 14 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 4 b) :=
  xc m 15 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 5 b) :=
  xc m 15 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 14 b) :=
  xc m 15 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_16_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 16 a) (X m 4 b) :=
  xc m 16 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_16_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 16 a) (X m 5 b) :=
  xc m 16 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 4 b) :=
  xc m 17 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 5 b) :=
  xc m 17 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 4 b) :=
  xc m 20 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_20_5 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 5 b = X m 5 b * X m 20 a * X m 14 (a*b) :=
  xs m 20 5 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_20_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 14 b) :=
  xc m 20 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 15 b) :=
  xc m 20 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_21_4 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 4 b = X m 4 b * X m 21 a * X m 15 (a*b) :=
  xs m 21 4 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_21_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 5 b) :=
  xc m 21 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 15 b) :=
  xc m 21 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem left_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 4 1 * (X m 5 1 * (1)))))))))))) =
      X m 4 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 5 1 * (X m 15 ((v 15) + (v 21)) * (X m 20 (v 20) * (X m 14 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))) := by
  rw [(c_9_4 m (v 9) 1).left_comm]
  rw [(c_8_4 m (v 8) 1).left_comm]
  have h2 : X m 21 (v 21) * X m 4 1 = X m 4 1 * X m 21 (v 21) * X m 15 (v 21) := by
    have h := s_21_4 m (v 21) 1
    rw [show (v 21) * 1 = (v 21) by ring] at h
    exact h
  rw [swap_suffix h2]
  rw [(c_20_4 m (v 20) 1).left_comm]
  rw [(c_15_4 m (v 15) 1).left_comm]
  rw [(c_14_4 m (v 14) 1).left_comm]
  rw [(c_11_4 m (v 11) 1).left_comm]
  rw [(c_10_4 m (v 10) 1).left_comm]
  rw [(c_17_4 m (v 17) 1).left_comm]
  rw [(c_16_4 m (v 16) 1).left_comm]
  rw [(c_21_15 m (v 21) (v 21)).left_comm]
  rw [(c_20_15 m (v 20) (v 21)).left_comm]
  rw [add_suffix m 15 (v 15) (v 21),
    show (v 15) + (v 21) = ((v 15) + (v 21)) by ring]
  rw [(c_9_5 m (v 9) 1).left_comm]
  rw [(c_8_5 m (v 8) 1).left_comm]
  rw [(c_21_5 m (v 21) 1).left_comm]
  have h16 : X m 20 (v 20) * X m 5 1 = X m 5 1 * X m 20 (v 20) * X m 14 (v 20) := by
    have h := s_20_5 m (v 20) 1
    rw [show (v 20) * 1 = (v 20) by ring] at h
    exact h
  rw [swap_suffix h16]
  rw [(c_15_5 m ((v 15) + (v 21)) 1).left_comm]

private theorem left_1 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 5 1 * (X m 15 ((v 15) + (v 21)) * (X m 20 (v 20) * (X m 14 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))) =
      X m 4 1 * (X m 5 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 ((v 14) + (v 20)) * (X m 15 ((v 15) + (v 21)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))) := by
  rw [(c_14_5 m (v 14) 1).left_comm]
  rw [(c_11_5 m (v 11) 1).left_comm]
  rw [(c_10_5 m (v 10) 1).left_comm]
  rw [(c_17_5 m (v 17) 1).left_comm]
  rw [(c_16_5 m (v 16) 1).left_comm]
  rw [(c_20_14 m (v 20) (v 20)).left_comm]
  rw [(c_15_14 m ((v 15) + (v 21)) (v 20)).left_comm]
  rw [add_suffix m 14 (v 14) (v 20),
    show (v 14) + (v 20) = ((v 14) + (v 20)) by ring]

private theorem collect_left (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 4 1 * (X m 5 1 * (1)))))))))))) =
      splitWord m ![0, 0, 0, 0, 1, 1, 0, 0, (v 8), (v 9), (v 10), (v 11), 0, 0, ((v 14) + (v 20)), ((v 15) + (v 21)), (v 16), (v 17), 0, 0, (v 20), (v 21), 0, 0] := by
  have h := (left_0 m v).trans ((left_1 m v))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

private theorem collect_right (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 1 * (X m 5 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))) =
      splitWord m ![0, 0, 0, 0, 1, 1, 0, 0, (v 8), (v 9), (v 10), (v 11), 0, 0, (v 14), (v 15), (v 16), (v 17), 0, 0, (v 20), (v 21), 0, 0] := by
  simp only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, xz, one_mul]

/-- The indicated split coordinates vanish when the literal test word commutes. -/
theorem detect_centralseventh (m : ℕ) (v : Fin 24 → CoefficientField m)
    (hc : Commute (tailSplitWord m v) (rootWord m 1 1)) :
    v 21 = 0 := by
  have h : X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 4 1 * (X m 5 1 * (1)))))))))))) = X m 4 1 * (X m 5 1 * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))) := by
    simpa only [tailSplitWord, word_1, map_one, one_mul, mul_one, xz, mul_assoc] using hc.eq
  have he := (collect_left m v).symm.trans (h.trans (collect_right m v))
  have hv := splitWord_injective m he
  have h := congrFun hv 15
  change ((v 15) + (v 21)) = (v 15) at h
  linear_combination h

end ReeF4.EvenInvolutionGeometry.UnipotentCenter
