module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords
/-!
# Checked split-root collection for GLS3 Lemma 3.3.9

Every adjacent exchange uses the proved F₄ matrix relations. Unique positive
split coordinates give the displayed scalar equations. The generator under
`RootCalculations/source` is only a proof-writing tool.
Source: GLS3 2.4.5(d), 2.4.6 and Lemma 3.3.9,
`refs/KGroup/GLS3/chapter2.tex` and `chapter3.tex`.
-/
public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.RootCalculations.CrossCollection
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent.OuterElimination
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local irreducible] X
private theorem c_2_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 11 b) :=
  xc m 2 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_2_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 16 b) :=
  xc m 2 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_2_17 (m : ℕ) (a b : CoefficientField m) :
    X m 2 a * X m 17 b = X m 17 b * X m 2 a * X m 8 (a*b) :=
  xs m 2 17 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_3_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 2 b) :=
  xc m 3 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_3_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 10 b) :=
  xc m 3 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_3_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 11 b) :=
  xc m 3 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_3_16 (m : ℕ) (a b : CoefficientField m) :
    X m 3 a * X m 16 b = X m 16 b * X m 3 a * X m 9 (a*b) :=
  xs m 3 16 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_3_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 17 b) :=
  xc m 3 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 2 b) :=
  xc m 8 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 3 b) :=
  xc m 8 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 10 b) :=
  xc m 8 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 15 b) :=
  xc m 8 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 20 b) :=
  xc m 8 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 21 b) :=
  xc m 8 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_8 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 8 b) :=
  xc m 9 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 17 b) :=
  xc m 9 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 20 b) :=
  xc m 9 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 21 b) :=
  xc m 9 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 2 b) :=
  xc m 14 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 3 b) :=
  xc m 14 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 10 b) :=
  xc m 14 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 11 b) :=
  xc m 14 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 2 b) :=
  xc m 15 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 3 b) :=
  xc m 15 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 5 b) :=
  xc m 15 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 10 b) :=
  xc m 15 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 11 b) :=
  xc m 15 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem s_20_2 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 2 b = X m 2 b * X m 20 a * X m 11 (a*b) :=
  xs m 20 2 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_20_3 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 3 b = X m 3 b * X m 20 a * X m 8 (a*b) * X m 15 (b*a^2) := by
  simpa only [mul_comm] using xb m 3 20 8 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_20_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 4 b) :=
  xc m 20 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_20_5 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 5 b = X m 5 b * X m 20 a * X m 14 (a*b) :=
  xs m 20 5 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

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

private theorem s_21_2 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 2 b = X m 2 b * X m 21 a * X m 14 (a*b) * X m 9 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 21 2 14 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 14 (a*b)) (xx m 9 (a*b^2))
    (xc m 14 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem s_21_3 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 3 b = X m 3 b * X m 21 a * X m 10 (a*b) :=
  xs m 21 3 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_21_4 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 4 b = X m 4 b * X m 21 a * X m 15 (a*b) :=
  xs m 21 4 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_21_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 5 b) :=
  xc m 21 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 10 b) :=
  xc m 21 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 14 b) :=
  xc m 21 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 15 b) :=
  xc m 21 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 20 b) :=
  xc m 21 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem left_0 (m : ℕ) (v : Fin 8 → CoefficientField m) :
    X m 4 (v 0) * (X m 5 (v 1) * (X m 3 (v 2) * (X m 2 (v 3) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (1)))))))) =
      X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 2 (v 3) * (X m 3 (v 2) * (X m 20 (v 7) * (X m 21 (v 6) * (X m 8 ((v 3) * (v 5)) * (X m 9 ((v 2) * (v 4)) * (1)))))))))) := by
  rw [(c_3_2 m (v 2) (v 3)).left_comm]
  have h1 : X m 3 (v 2) * X m 16 (v 4) = X m 16 (v 4) * X m 3 (v 2) * X m 9 ((v 2) * (v 4)) := by
    have h := s_3_16 m (v 2) (v 4)
    rw [show (v 2) * (v 4) = ((v 2) * (v 4)) by ring] at h
    exact h
  rw [swap_suffix h1]
  rw [(c_2_16 m (v 3) (v 4)).left_comm]
  rw [(c_9_17 m ((v 2) * (v 4)) (v 5)).left_comm]
  rw [(c_3_17 m (v 2) (v 5)).left_comm]
  have h5 : X m 2 (v 3) * X m 17 (v 5) = X m 17 (v 5) * X m 2 (v 3) * X m 8 ((v 3) * (v 5)) := by
    have h := s_2_17 m (v 3) (v 5)
    rw [show (v 3) * (v 5) = ((v 3) * (v 5)) by ring] at h
    exact h
  rw [swap_suffix h5]
  rw [(c_8_3 m ((v 3) * (v 5)) (v 2)).left_comm]
  rw [(c_9_21 m ((v 2) * (v 4)) (v 6)).left_comm]
  rw [(c_8_21 m ((v 3) * (v 5)) (v 6)).left_comm]
  rw [(c_9_20 m ((v 2) * (v 4)) (v 7)).left_comm]
  rw [(c_8_20 m ((v 3) * (v 5)) (v 7)).left_comm]
  rw [(c_21_20 m (v 6) (v 7)).left_comm]

private theorem collect_left (m : ℕ) (v : Fin 8 → CoefficientField m) :
    X m 4 (v 0) * (X m 5 (v 1) * (X m 3 (v 2) * (X m 2 (v 3) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (1)))))))) =
      splitWord m ![0, 0, (v 3), (v 2), (v 0), (v 1), 0, 0, ((v 3) * (v 5)), ((v 2) * (v 4)), 0, 0, 0, 0, 0, 0, (v 4), (v 5), 0, 0, (v 7), (v 6), 0, 0] := by
  have h := (left_0 m v)
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

private theorem right_0 (m : ℕ) (v : Fin 8 → CoefficientField m) :
    X m 16 (v 4) * (X m 17 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 3 (v 2) * (X m 2 (v 3) * (1)))))))) =
      X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 3 (v 2) * (X m 14 ((v 1) * (v 7)) * (X m 15 ((v 0) * (v 6)) * (X m 20 (v 7) * (X m 8 ((v 2) * (v 7)) * (X m 15 ((v 2) * ((v 7) ^ 2)) * (X m 21 (v 6) * (X m 10 ((v 2) * (v 6)) * (X m 2 (v 3) * (1))))))))))))) := by
  rw [(c_21_20 m (v 6) (v 7)).left_comm]
  have h1 : X m 21 (v 6) * X m 4 (v 0) = X m 4 (v 0) * X m 21 (v 6) * X m 15 ((v 0) * (v 6)) := by
    have h := s_21_4 m (v 6) (v 0)
    rw [show (v 6) * (v 0) = ((v 0) * (v 6)) by ring] at h
    exact h
  rw [swap_suffix h1]
  rw [(c_20_4 m (v 7) (v 0)).left_comm]
  rw [(c_17_4 m (v 5) (v 0)).left_comm]
  rw [(c_16_4 m (v 4) (v 0)).left_comm]
  rw [(c_21_15 m (v 6) ((v 0) * (v 6))).left_comm]
  rw [(c_20_15 m (v 7) ((v 0) * (v 6))).left_comm]
  rw [(c_21_5 m (v 6) (v 1)).left_comm]
  have h8 : X m 20 (v 7) * X m 5 (v 1) = X m 5 (v 1) * X m 20 (v 7) * X m 14 ((v 1) * (v 7)) := by
    have h := s_20_5 m (v 7) (v 1)
    rw [show (v 7) * (v 1) = ((v 1) * (v 7)) by ring] at h
    exact h
  rw [swap_suffix h8]
  rw [(c_15_5 m ((v 0) * (v 6)) (v 1)).left_comm]
  rw [(c_17_5 m (v 5) (v 1)).left_comm]
  rw [(c_16_5 m (v 4) (v 1)).left_comm]
  rw [(c_20_14 m (v 7) ((v 1) * (v 7))).left_comm]
  rw [(c_15_14 m ((v 0) * (v 6)) ((v 1) * (v 7))).left_comm]
  have h14 : X m 21 (v 6) * X m 3 (v 2) = X m 3 (v 2) * X m 21 (v 6) * X m 10 ((v 2) * (v 6)) := by
    have h := s_21_3 m (v 6) (v 2)
    rw [show (v 6) * (v 2) = ((v 2) * (v 6)) by ring] at h
    exact h
  rw [swap_suffix h14]
  have h15 : X m 20 (v 7) * X m 3 (v 2) = X m 3 (v 2) * X m 20 (v 7) * X m 8 ((v 2) * (v 7)) * X m 15 ((v 2) * ((v 7) ^ 2)) := by
    have h := s_20_3 m (v 7) (v 2)
    rw [show (v 7) * (v 2) = ((v 2) * (v 7)) by ring, show (v 2) * (v 7) ^ 2 = ((v 2) * ((v 7) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h15]
  rw [(c_15_3 m ((v 0) * (v 6)) (v 2)).left_comm]
  rw [(c_14_3 m ((v 1) * (v 7)) (v 2)).left_comm]

private theorem right_1 (m : ℕ) (v : Fin 8 → CoefficientField m) :
    X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 3 (v 2) * (X m 14 ((v 1) * (v 7)) * (X m 15 ((v 0) * (v 6)) * (X m 20 (v 7) * (X m 8 ((v 2) * (v 7)) * (X m 15 ((v 2) * ((v 7) ^ 2)) * (X m 21 (v 6) * (X m 10 ((v 2) * (v 6)) * (X m 2 (v 3) * (1))))))))))))) =
      X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 ((v 2) * (v 6)) * (X m 2 (v 3) * (X m 3 (v 2) * (X m 14 ((v 1) * (v 7)) * (X m 11 ((v 3) * (v 7)) * (X m 15 (((v 0) * (v 6)) + ((v 2) * ((v 7) ^ 2))) * (X m 20 (v 7) * (X m 21 (v 6) * (X m 14 ((v 3) * (v 6)) * (X m 9 ((v 6) * ((v 3) ^ 2)) * (X m 8 ((v 2) * (v 7)) * (1))))))))))))))) := by
  rw [(c_8_15 m ((v 2) * (v 7)) ((v 2) * ((v 7) ^ 2))).left_comm]
  rw [(c_20_15 m (v 7) ((v 2) * ((v 7) ^ 2))).left_comm]
  rw [add_suffix m 15 ((v 0) * (v 6)) ((v 2) * ((v 7) ^ 2)),
    show ((v 0) * (v 6)) + ((v 2) * ((v 7) ^ 2)) = (((v 0) * (v 6)) + ((v 2) * ((v 7) ^ 2))) by ring]
  rw [(c_8_21 m ((v 2) * (v 7)) (v 6)).left_comm]
  rw [(c_8_10 m ((v 2) * (v 7)) ((v 2) * (v 6))).left_comm]
  rw [(c_21_10 m (v 6) ((v 2) * (v 6))).left_comm]
  rw [(c_20_10 m (v 7) ((v 2) * (v 6))).left_comm]
  rw [(c_15_10 m (((v 0) * (v 6)) + ((v 2) * ((v 7) ^ 2))) ((v 2) * (v 6))).left_comm]
  rw [(c_14_10 m ((v 1) * (v 7)) ((v 2) * (v 6))).left_comm]
  rw [(c_3_10 m (v 2) ((v 2) * (v 6))).left_comm]
  rw [(c_8_2 m ((v 2) * (v 7)) (v 3)).left_comm]
  have h11 : X m 21 (v 6) * X m 2 (v 3) = X m 2 (v 3) * X m 21 (v 6) * X m 14 ((v 3) * (v 6)) * X m 9 ((v 6) * ((v 3) ^ 2)) := by
    have h := s_21_2 m (v 6) (v 3)
    rw [show (v 6) * (v 3) = ((v 3) * (v 6)) by ring, show (v 6) * (v 3) ^ 2 = ((v 6) * ((v 3) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h11]
  have h12 : X m 20 (v 7) * X m 2 (v 3) = X m 2 (v 3) * X m 20 (v 7) * X m 11 ((v 3) * (v 7)) := by
    have h := s_20_2 m (v 7) (v 3)
    rw [show (v 7) * (v 3) = ((v 3) * (v 7)) by ring] at h
    exact h
  rw [swap_suffix h12]
  rw [(c_15_2 m (((v 0) * (v 6)) + ((v 2) * ((v 7) ^ 2))) (v 3)).left_comm]
  rw [(c_14_2 m ((v 1) * (v 7)) (v 3)).left_comm]
  rw [(c_3_2 m (v 2) (v 3)).left_comm]
  rw [(c_20_11 m (v 7) ((v 3) * (v 7))).left_comm]
  rw [(c_15_11 m (((v 0) * (v 6)) + ((v 2) * ((v 7) ^ 2))) ((v 3) * (v 7))).left_comm]

private theorem right_2 (m : ℕ) (v : Fin 8 → CoefficientField m) :
    X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 ((v 2) * (v 6)) * (X m 2 (v 3) * (X m 3 (v 2) * (X m 14 ((v 1) * (v 7)) * (X m 11 ((v 3) * (v 7)) * (X m 15 (((v 0) * (v 6)) + ((v 2) * ((v 7) ^ 2))) * (X m 20 (v 7) * (X m 21 (v 6) * (X m 14 ((v 3) * (v 6)) * (X m 9 ((v 6) * ((v 3) ^ 2)) * (X m 8 ((v 2) * (v 7)) * (1))))))))))))))) =
      X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 ((v 2) * (v 6)) * (X m 11 ((v 3) * (v 7)) * (X m 2 (v 3) * (X m 3 (v 2) * (X m 14 (((v 1) * (v 7)) + ((v 3) * (v 6))) * (X m 15 (((v 0) * (v 6)) + ((v 2) * ((v 7) ^ 2))) * (X m 20 (v 7) * (X m 21 (v 6) * (X m 8 ((v 2) * (v 7)) * (X m 9 ((v 6) * ((v 3) ^ 2)) * (1)))))))))))))) := by
  rw [(c_14_11 m ((v 1) * (v 7)) ((v 3) * (v 7))).left_comm]
  rw [(c_3_11 m (v 2) ((v 3) * (v 7))).left_comm]
  rw [(c_2_11 m (v 3) ((v 3) * (v 7))).left_comm]
  rw [(c_21_14 m (v 6) ((v 3) * (v 6))).left_comm]
  rw [(c_20_14 m (v 7) ((v 3) * (v 6))).left_comm]
  rw [(c_15_14 m (((v 0) * (v 6)) + ((v 2) * ((v 7) ^ 2))) ((v 3) * (v 6))).left_comm]
  rw [add_suffix m 14 ((v 1) * (v 7)) ((v 3) * (v 6)),
    show ((v 1) * (v 7)) + ((v 3) * (v 6)) = (((v 1) * (v 7)) + ((v 3) * (v 6))) by ring]
  rw [(c_9_8 m ((v 6) * ((v 3) ^ 2)) ((v 2) * (v 7))).left_comm]

private theorem collect_right (m : ℕ) (v : Fin 8 → CoefficientField m) :
    X m 16 (v 4) * (X m 17 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 3 (v 2) * (X m 2 (v 3) * (1)))))))) =
      splitWord m ![0, 0, (v 3), (v 2), (v 0), (v 1), 0, 0, ((v 2) * (v 7)), ((v 6) * ((v 3) ^ 2)), ((v 2) * (v 6)), ((v 3) * (v 7)), 0, 0, (((v 1) * (v 7)) + ((v 3) * (v 6))), (((v 0) * (v 6)) + ((v 2) * ((v 7) ^ 2))), (v 4), (v 5), 0, 0, (v 7), (v 6), 0, 0] := by
  have h := (right_0 m v).trans ((right_1 m v).trans ((right_2 m v)))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

/-- Scalar consequences of commutation of the displayed literal split words. -/
theorem equations (m : ℕ) (v : Fin 8 → CoefficientField m)
    (hc : Commute (X m 4 (v 0) * (X m 5 (v 1) * (X m 3 (v 2) * (X m 2 (v 3) * (1))))) (X m 16 (v 4) * (X m 17 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (1)))))) :
    ((v 2) * (v 6)) = 0 ∧ (((v 2) * (v 4)) + ((v 6) * ((v 3) ^ 2))) = 0 := by
  have hh : X m 4 (v 0) * (X m 5 (v 1) * (X m 3 (v 2) * (X m 2 (v 3) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (1)))))))) = X m 16 (v 4) * (X m 17 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 3 (v 2) * (X m 2 (v 3) * (1)))))))) := by
    simpa only [mul_assoc, one_mul] using hc.eq
  have hv := splitWord_injective m ((collect_left m v).symm.trans (hh.trans (collect_right m v)))
  constructor
  · have h := congrFun hv 10
    change 0 = ((v 2) * (v 6)) at h
    linear_combination (norm := (ring_nf; simp only [CharTwo.two_eq_zero, mul_zero])) h
  · have h := congrFun hv 9
    change ((v 2) * (v 4)) = ((v 6) * ((v 3) ^ 2)) at h
    linear_combination (norm := (ring_nf; simp only [CharTwo.two_eq_zero, mul_zero])) h

end ReeF4.ElementaryTwoBound.RootCalculations.CrossCollection
