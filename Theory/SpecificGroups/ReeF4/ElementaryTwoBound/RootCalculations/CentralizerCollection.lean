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
namespace ReeF4.ElementaryTwoBound.RootCalculations.CentralizerCollection
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent.OuterElimination
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local irreducible] X
private theorem c_2_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 4 b) :=
  xc m 2 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_2_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 5 b) :=
  xc m 2 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_3_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 4 b) :=
  xc m 3 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_3_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 5 b) :=
  xc m 3 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_5_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 5 a) (X m 4 b) :=
  xc m 5 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 4 b) :=
  xc m 6 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 5 b) :=
  xc m 6 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 4 b) :=
  xc m 7 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 5 b) :=
  xc m 7 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 4 b) :=
  xc m 8 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 5 b) :=
  xc m 8 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 6 b) :=
  xc m 8 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_7 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 7 b) :=
  xc m 8 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 14 b) :=
  xc m 8 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 15 b) :=
  xc m 8 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 20 b) :=
  xc m 8 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 21 b) :=
  xc m 8 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 4 b) :=
  xc m 9 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 5 b) :=
  xc m 9 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 6 b) :=
  xc m 9 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_7 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 7 b) :=
  xc m 9 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_8 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 8 b) :=
  xc m 9 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 13 b) :=
  xc m 9 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 14 b) :=
  xc m 9 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 15 b) :=
  xc m 9 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 20 b) :=
  xc m 9 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 21 b) :=
  xc m 9 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem s_12_4 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 4 b = X m 4 b * X m 12 a * X m 9 (a*b) :=
  xs m 12 4 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_12_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 5 b) :=
  xc m 12 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 4 b) :=
  xc m 13 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_13_5 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 5 b = X m 5 b * X m 13 a * X m 8 (a*b) :=
  xs m 13 5 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

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

private theorem left_0 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 4 (v 24) * (X m 5 (v 25) * (1)))))))))))))))))))) =
      X m 4 ((v 24) + (v 4)) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 9 ((v 12) * (v 24)) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 24)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 25) * (1))))))))))))))))))))) := by
  rw [(c_9_4 m (v 9) (v 24)).left_comm]
  rw [(c_8_4 m (v 8) (v 24)).left_comm]
  rw [(c_7_4 m (v 7) (v 24)).left_comm]
  rw [(c_6_4 m (v 6) (v 24)).left_comm]
  have h4 : X m 21 (v 21) * X m 4 (v 24) = X m 4 (v 24) * X m 21 (v 21) * X m 15 ((v 21) * (v 24)) := by
    have h := s_21_4 m (v 21) (v 24)
    rw [show (v 21) * (v 24) = ((v 21) * (v 24)) by ring] at h
    exact h
  rw [swap_suffix h4]
  rw [(c_20_4 m (v 20) (v 24)).left_comm]
  rw [(c_15_4 m (v 15) (v 24)).left_comm]
  rw [(c_14_4 m (v 14) (v 24)).left_comm]
  rw [(c_13_4 m (v 13) (v 24)).left_comm]
  have h9 : X m 12 (v 12) * X m 4 (v 24) = X m 4 (v 24) * X m 12 (v 12) * X m 9 ((v 12) * (v 24)) := by
    have h := s_12_4 m (v 12) (v 24)
    rw [show (v 12) * (v 24) = ((v 12) * (v 24)) by ring] at h
    exact h
  rw [swap_suffix h9]
  rw [(c_3_4 m (v 3) (v 24)).left_comm]
  rw [(c_2_4 m (v 2) (v 24)).left_comm]
  rw [(c_11_4 m (v 11) (v 24)).left_comm]
  rw [(c_10_4 m (v 10) (v 24)).left_comm]
  rw [(c_17_4 m (v 17) (v 24)).left_comm]
  rw [(c_16_4 m (v 16) (v 24)).left_comm]
  rw [(c_5_4 m (v 5) (v 24)).left_comm]
  rw [add_suffix m 4 (v 4) (v 24),
    show (v 4) + (v 24) = ((v 24) + (v 4)) by ring]

private theorem left_1 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 4 ((v 24) + (v 4)) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 9 ((v 12) * (v 24)) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 24)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 25) * (1))))))))))))))))))))) =
      X m 4 ((v 24) + (v 4)) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 24))) * (X m 20 (v 20) * (X m 5 (v 25) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + ((v 12) * (v 24))) * (1))))))))))))))))))) := by
  rw [(c_9_13 m ((v 12) * (v 24)) (v 13)).left_comm]
  rw [(c_9_14 m ((v 12) * (v 24)) (v 14)).left_comm]
  rw [(c_9_15 m ((v 12) * (v 24)) (v 15)).left_comm]
  rw [(c_9_20 m ((v 12) * (v 24)) (v 20)).left_comm]
  rw [(c_9_21 m ((v 12) * (v 24)) (v 21)).left_comm]
  rw [(c_9_15 m ((v 12) * (v 24)) ((v 21) * (v 24))).left_comm]
  rw [(c_21_15 m (v 21) ((v 21) * (v 24))).left_comm]
  rw [(c_20_15 m (v 20) ((v 21) * (v 24))).left_comm]
  rw [add_suffix m 15 (v 15) ((v 21) * (v 24)),
    show (v 15) + ((v 21) * (v 24)) = ((v 15) + ((v 21) * (v 24))) by ring]
  rw [(c_9_6 m ((v 12) * (v 24)) (v 6)).left_comm]
  rw [(c_9_7 m ((v 12) * (v 24)) (v 7)).left_comm]
  rw [(c_9_8 m ((v 12) * (v 24)) (v 8)).left_comm]
  rw [add_suffix m 9 ((v 12) * (v 24)) (v 9),
    show ((v 12) * (v 24)) + (v 9) = ((v 9) + ((v 12) * (v 24))) by ring]
  rw [(c_9_5 m ((v 9) + ((v 12) * (v 24))) (v 25)).left_comm]
  rw [(c_8_5 m (v 8) (v 25)).left_comm]
  rw [(c_7_5 m (v 7) (v 25)).left_comm]
  rw [(c_6_5 m (v 6) (v 25)).left_comm]
  rw [(c_21_5 m (v 21) (v 25)).left_comm]

private theorem left_2 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 4 ((v 24) + (v 4)) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 24))) * (X m 20 (v 20) * (X m 5 (v 25) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + ((v 12) * (v 24))) * (1))))))))))))))))))) =
      X m 4 ((v 24) + (v 4)) * (X m 5 ((v 25) + (v 5)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 14 ((v 20) * (v 25)) * (X m 15 ((v 15) + ((v 21) * (v 24))) * (X m 20 (v 20) * (X m 8 ((v 13) * (v 25)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + ((v 12) * (v 24))) * (1)))))))))))))))))))) := by
  have h0 : X m 20 (v 20) * X m 5 (v 25) = X m 5 (v 25) * X m 20 (v 20) * X m 14 ((v 20) * (v 25)) := by
    have h := s_20_5 m (v 20) (v 25)
    rw [show (v 20) * (v 25) = ((v 20) * (v 25)) by ring] at h
    exact h
  rw [swap_suffix h0]
  rw [(c_15_5 m ((v 15) + ((v 21) * (v 24))) (v 25)).left_comm]
  rw [(c_14_5 m (v 14) (v 25)).left_comm]
  have h3 : X m 13 (v 13) * X m 5 (v 25) = X m 5 (v 25) * X m 13 (v 13) * X m 8 ((v 13) * (v 25)) := by
    have h := s_13_5 m (v 13) (v 25)
    rw [show (v 13) * (v 25) = ((v 13) * (v 25)) by ring] at h
    exact h
  rw [swap_suffix h3]
  rw [(c_12_5 m (v 12) (v 25)).left_comm]
  rw [(c_3_5 m (v 3) (v 25)).left_comm]
  rw [(c_2_5 m (v 2) (v 25)).left_comm]
  rw [(c_11_5 m (v 11) (v 25)).left_comm]
  rw [(c_10_5 m (v 10) (v 25)).left_comm]
  rw [(c_17_5 m (v 17) (v 25)).left_comm]
  rw [(c_16_5 m (v 16) (v 25)).left_comm]
  rw [add_suffix m 5 (v 5) (v 25),
    show (v 5) + (v 25) = ((v 25) + (v 5)) by ring]
  rw [(c_8_14 m ((v 13) * (v 25)) (v 14)).left_comm]
  rw [(c_8_15 m ((v 13) * (v 25)) ((v 15) + ((v 21) * (v 24)))).left_comm]
  rw [(c_8_20 m ((v 13) * (v 25)) (v 20)).left_comm]
  rw [(c_8_14 m ((v 13) * (v 25)) ((v 20) * (v 25))).left_comm]
  rw [(c_20_14 m (v 20) ((v 20) * (v 25))).left_comm]
  rw [(c_15_14 m ((v 15) + ((v 21) * (v 24))) ((v 20) * (v 25))).left_comm]

private theorem left_3 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 4 ((v 24) + (v 4)) * (X m 5 ((v 25) + (v 5)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 14 ((v 20) * (v 25)) * (X m 15 ((v 15) + ((v 21) * (v 24))) * (X m 20 (v 20) * (X m 8 ((v 13) * (v 25)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + ((v 12) * (v 24))) * (1)))))))))))))))))))) =
      X m 4 ((v 24) + (v 4)) * (X m 5 ((v 25) + (v 5)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 25))) * (X m 15 ((v 15) + ((v 21) * (v 24))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 25))) * (X m 9 ((v 9) + ((v 12) * (v 24))) * (1)))))))))))))))))) := by
  rw [add_suffix m 14 (v 14) ((v 20) * (v 25)),
    show (v 14) + ((v 20) * (v 25)) = ((v 14) + ((v 20) * (v 25))) by ring]
  rw [(c_8_21 m ((v 13) * (v 25)) (v 21)).left_comm]
  rw [(c_8_6 m ((v 13) * (v 25)) (v 6)).left_comm]
  rw [(c_8_7 m ((v 13) * (v 25)) (v 7)).left_comm]
  rw [add_suffix m 8 ((v 13) * (v 25)) (v 8),
    show ((v 13) * (v 25)) + (v 8) = ((v 8) + ((v 13) * (v 25))) by ring]

private theorem collect_left (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 4 (v 24) * (X m 5 (v 25) * (1)))))))))))))))))))) =
      splitWord m ![0, 0, (v 2), (v 3), ((v 24) + (v 4)), ((v 25) + (v 5)), (v 6), (v 7), ((v 8) + ((v 13) * (v 25))), ((v 9) + ((v 12) * (v 24))), (v 10), (v 11), (v 12), (v 13), ((v 14) + ((v 20) * (v 25))), ((v 15) + ((v 21) * (v 24))), (v 16), (v 17), 0, 0, (v 20), (v 21), 0, 0] := by
  have h := (left_0 m v).trans ((left_1 m v).trans ((left_2 m v).trans ((left_3 m v))))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

private theorem right_0 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 4 (v 24) * (X m 5 (v 25) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))) =
      X m 4 ((v 24) + (v 4)) * (X m 5 ((v 25) + (v 5)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))) := by
  rw [(c_5_4 m (v 25) (v 4)).left_comm]
  rw [add_suffix m 4 (v 24) (v 4),
    show (v 24) + (v 4) = ((v 24) + (v 4)) by ring]
  rw [add_suffix m 5 (v 25) (v 5),
    show (v 25) + (v 5) = ((v 25) + (v 5)) by ring]

private theorem collect_right (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 4 (v 24) * (X m 5 (v 25) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))) =
      splitWord m ![0, 0, (v 2), (v 3), ((v 24) + (v 4)), ((v 25) + (v 5)), (v 6), (v 7), (v 8), (v 9), (v 10), (v 11), (v 12), (v 13), (v 14), (v 15), (v 16), (v 17), 0, 0, (v 20), (v 21), 0, 0] := by
  have h := (right_0 m v)
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

/-- Scalar consequences of commutation of the displayed literal split words. -/
theorem equations (m : ℕ) (v : Fin 26 → CoefficientField m)
    (hc : Commute (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))) (X m 4 (v 24) * (X m 5 (v 25) * (1)))) :
    ((v 21) * (v 24)) = 0 := by
  have hh : X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 4 (v 24) * (X m 5 (v 25) * (1)))))))))))))))))))) = X m 4 (v 24) * (X m 5 (v 25) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))) := by
    simpa only [mul_assoc, one_mul] using hc.eq
  have hv := splitWord_injective m ((collect_left m v).symm.trans (hh.trans (collect_right m v)))
  have h := congrFun hv 15
  change ((v 15) + ((v 21) * (v 24))) = (v 15) at h
  linear_combination h

end ReeF4.ElementaryTwoBound.RootCalculations.CentralizerCollection
