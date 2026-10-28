module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords
/-!
Checked split-root collection for outer-coordinate elimination.
Each adjacent exchange is an instance of the actual split F₄ matrix relation;
the final coordinate comparison uses unique positive split coordinates.
Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/
public section
noncomputable section
namespace ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local irreducible] X

private theorem s_0_10 (m : ℕ) (a b : CoefficientField m) :
    X m 0 a * X m 10 b = X m 10 b * X m 0 a * X m 9 (a*b) :=
  xs m 0 10 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_0_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 0 a) (X m 11 b) :=
  xc m 0 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_1_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 1 a) (X m 10 b) :=
  xc m 1 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_1_11 (m : ℕ) (a b : CoefficientField m) :
    X m 1 a * X m 11 b = X m 11 b * X m 1 a * X m 8 (a*b) :=
  xs m 1 11 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_2_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 10 b) :=
  xc m 2 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_2_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 11 b) :=
  xc m 2 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_3_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 10 b) :=
  xc m 3 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_3_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 11 b) :=
  xc m 3 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 10 b) :=
  xc m 6 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 11 b) :=
  xc m 6 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 10 b) :=
  xc m 7 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 11 b) :=
  xc m 7 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 2 b) :=
  xc m 8 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 3 b) :=
  xc m 8 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_8_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 12 b) :=
  xc m 8 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 13 b) :=
  xc m 8 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 14 b) :=
  xc m 8 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 15 b) :=
  xc m 8 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 18 b) :=
  xc m 8 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 19 b) :=
  xc m 8 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 20 b) :=
  xc m 8 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 21 b) :=
  xc m 8 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 1 b) :=
  xc m 9 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 2 b) :=
  xc m 9 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 3 b) :=
  xc m 9 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 6 b) :=
  xc m 9 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_7 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 7 b) :=
  xc m 9 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_8 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 8 b) :=
  xc m 9 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 10 b) :=
  xc m 9 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 11 b) :=
  xc m 9 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 12 b) :=
  xc m 9 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 13 b) :=
  xc m 9 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 14 b) :=
  xc m 9 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 15 b) :=
  xc m 9 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 18 b) :=
  xc m 9 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 19 b) :=
  xc m 9 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_10_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 16 b) :=
  xc m 10 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_10_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 17 b) :=
  xc m 10 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_10_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 22 b) :=
  xc m 10 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_10_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 23 b) :=
  xc m 10 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 4 b) :=
  xc m 11 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 5 b) :=
  xc m 11 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 10 b) :=
  xc m 11 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 16 b) :=
  xc m 11 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 17 b) :=
  xc m 11 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 22 b) :=
  xc m 11 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 23 b) :=
  xc m 11 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 10 b) :=
  xc m 12 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 11 b) :=
  xc m 12 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 10 b) :=
  xc m 13 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 11 b) :=
  xc m 13 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_19_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 10 b) :=
  xc m 19 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_19_11 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 11 b = X m 11 b * X m 19 a * X m 14 (a*b) :=
  xs m 19 11 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_19_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 14 b) :=
  xc m 19 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 10 b) :=
  xc m 20 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 11 b) :=
  xc m 20 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 10 b) :=
  xc m 21 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 11 b) :=
  xc m 21 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem left_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 10 1 * (X m 11 1 * (1)))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (1 + (v 10)) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 9 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 15 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 11 1 * (1))))))))))))))))))))))))))) := by
  rw [(c_9_10 m (v 9) 1).left_comm]
  rw [(c_8_10 m (v 8) 1).left_comm]
  rw [(c_7_10 m (v 7) 1).left_comm]
  rw [(c_6_10 m (v 6) 1).left_comm]
  rw [(c_21_10 m (v 21) 1).left_comm]
  rw [(c_20_10 m (v 20) 1).left_comm]
  rw [(c_19_10 m (v 19) 1).left_comm]
  have h7 : X m 18 (v 18) * X m 10 1 = X m 10 1 * X m 18 (v 18) * X m 15 (v 18) := by
    have h := s_18_10 m (v 18) 1
    rw [show (v 18) * 1 = (v 18) by ring] at h
    exact h
  rw [swap_suffix h7]
  rw [(c_15_10 m (v 15) 1).left_comm]
  rw [(c_14_10 m (v 14) 1).left_comm]
  rw [(c_13_10 m (v 13) 1).left_comm]
  rw [(c_12_10 m (v 12) 1).left_comm]
  rw [(c_3_10 m (v 3) 1).left_comm]
  rw [(c_2_10 m (v 2) 1).left_comm]
  rw [(c_1_10 m (v 1) 1).left_comm]
  have h15 : X m 0 (v 0) * X m 10 1 = X m 10 1 * X m 0 (v 0) * X m 9 (v 0) := by
    have h := s_0_10 m (v 0) 1
    rw [show (v 0) * 1 = (v 0) by ring] at h
    exact h
  rw [swap_suffix h15]
  rw [(c_11_10 m (v 11) 1).left_comm]
  rw [add_suffix m 10 (v 10) 1,
    show (v 10) + 1 = (1 + (v 10)) by ring]

private theorem left_1 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (1 + (v 10)) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 9 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 15 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 11 1 * (1))))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (1 + (v 10)) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + (v 18)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 0) + (v 9)) * (X m 11 1 * (1))))))))))))))))))))))))) := by
  rw [(c_9_1 m (v 0) (v 1)).left_comm]
  rw [(c_9_2 m (v 0) (v 2)).left_comm]
  rw [(c_9_3 m (v 0) (v 3)).left_comm]
  rw [(c_9_12 m (v 0) (v 12)).left_comm]
  rw [(c_9_13 m (v 0) (v 13)).left_comm]
  rw [(c_9_14 m (v 0) (v 14)).left_comm]
  rw [(c_9_15 m (v 0) (v 15)).left_comm]
  rw [(c_9_18 m (v 0) (v 18)).left_comm]
  rw [(c_9_15 m (v 0) (v 18)).left_comm]
  rw [(c_18_15 m (v 18) (v 18)).left_comm]
  rw [add_suffix m 15 (v 15) (v 18),
    show (v 15) + (v 18) = ((v 15) + (v 18)) by ring]
  rw [(c_9_19 m (v 0) (v 19)).left_comm]
  rw [(c_9_20 m (v 0) (v 20)).left_comm]
  rw [(c_9_21 m (v 0) (v 21)).left_comm]
  rw [(c_9_6 m (v 0) (v 6)).left_comm]
  rw [(c_9_7 m (v 0) (v 7)).left_comm]
  rw [(c_9_8 m (v 0) (v 8)).left_comm]
  rw [add_suffix m 9 (v 0) (v 9),
    show (v 0) + (v 9) = ((v 0) + (v 9)) by ring]

private theorem left_2 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (1 + (v 10)) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + (v 18)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 0) + (v 9)) * (X m 11 1 * (1))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (1 + (v 10)) * (X m 11 (1 + (v 11)) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 8 (v 1) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + (v 18)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 0) + (v 9)) * (1)))))))))))))))))))))))))) := by
  rw [(c_9_11 m ((v 0) + (v 9)) 1).left_comm]
  rw [(c_8_11 m (v 8) 1).left_comm]
  rw [(c_7_11 m (v 7) 1).left_comm]
  rw [(c_6_11 m (v 6) 1).left_comm]
  rw [(c_21_11 m (v 21) 1).left_comm]
  rw [(c_20_11 m (v 20) 1).left_comm]
  have h6 : X m 19 (v 19) * X m 11 1 = X m 11 1 * X m 19 (v 19) * X m 14 (v 19) := by
    have h := s_19_11 m (v 19) 1
    rw [show (v 19) * 1 = (v 19) by ring] at h
    exact h
  rw [swap_suffix h6]
  rw [(c_18_11 m (v 18) 1).left_comm]
  rw [(c_15_11 m ((v 15) + (v 18)) 1).left_comm]
  rw [(c_14_11 m (v 14) 1).left_comm]
  rw [(c_13_11 m (v 13) 1).left_comm]
  rw [(c_12_11 m (v 12) 1).left_comm]
  rw [(c_3_11 m (v 3) 1).left_comm]
  rw [(c_2_11 m (v 2) 1).left_comm]
  have h14 : X m 1 (v 1) * X m 11 1 = X m 11 1 * X m 1 (v 1) * X m 8 (v 1) := by
    have h := s_1_11 m (v 1) 1
    rw [show (v 1) * 1 = (v 1) by ring] at h
    exact h
  rw [swap_suffix h14]
  rw [(c_0_11 m (v 0) 1).left_comm]
  rw [add_suffix m 11 (v 11) 1,
    show (v 11) + 1 = (1 + (v 11)) by ring]
  rw [(c_8_2 m (v 1) (v 2)).left_comm]

private theorem left_3 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (1 + (v 10)) * (X m 11 (1 + (v 11)) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 8 (v 1) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + (v 18)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 0) + (v 9)) * (1)))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (1 + (v 10)) * (X m 11 (1 + (v 11)) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + (v 19)) * (X m 15 ((v 15) + (v 18)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 1) + (v 8)) * (X m 9 ((v 0) + (v 9)) * (1)))))))))))))))))))))))) := by
  rw [(c_8_3 m (v 1) (v 3)).left_comm]
  rw [(c_8_12 m (v 1) (v 12)).left_comm]
  rw [(c_8_13 m (v 1) (v 13)).left_comm]
  rw [(c_8_14 m (v 1) (v 14)).left_comm]
  rw [(c_8_15 m (v 1) ((v 15) + (v 18))).left_comm]
  rw [(c_8_18 m (v 1) (v 18)).left_comm]
  rw [(c_8_19 m (v 1) (v 19)).left_comm]
  rw [(c_8_14 m (v 1) (v 19)).left_comm]
  rw [(c_19_14 m (v 19) (v 19)).left_comm]
  rw [(c_18_14 m (v 18) (v 19)).left_comm]
  rw [(c_15_14 m ((v 15) + (v 18)) (v 19)).left_comm]
  rw [add_suffix m 14 (v 14) (v 19),
    show (v 14) + (v 19) = ((v 14) + (v 19)) by ring]
  rw [(c_8_20 m (v 1) (v 20)).left_comm]
  rw [(c_8_21 m (v 1) (v 21)).left_comm]
  rw [(c_8_6 m (v 1) (v 6)).left_comm]
  rw [(c_8_7 m (v 1) (v 7)).left_comm]
  rw [add_suffix m 8 (v 1) (v 8),
    show (v 1) + (v 8) = ((v 1) + (v 8)) by ring]

private theorem collect_left (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 10 1 * (X m 11 1 * (1)))))))))))))))))))))))))) =
      splitWord m ![(v 0), (v 1), (v 2), (v 3), (v 4), (v 5), (v 6), (v 7), ((v 1) + (v 8)), ((v 0) + (v 9)), (1 + (v 10)), (1 + (v 11)), (v 12), (v 13), ((v 14) + (v 19)), ((v 15) + (v 18)), (v 16), (v 17), (v 18), (v 19), (v 20), (v 21), (v 22), (v 23)] := by
  have h := (left_0 m v).trans ((left_1 m v).trans ((left_2 m v).trans ((left_3 m v))))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

private theorem right_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 1 * (X m 11 1 * (X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (1 + (v 10)) * (X m 11 (1 + (v 11)) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))) := by
  rw [(c_11_22 m 1 (v 22)).left_comm]
  rw [(c_10_22 m 1 (v 22)).left_comm]
  rw [(c_11_23 m 1 (v 23)).left_comm]
  rw [(c_10_23 m 1 (v 23)).left_comm]
  rw [(c_11_4 m 1 (v 4)).left_comm]
  rw [(c_10_4 m 1 (v 4)).left_comm]
  rw [(c_11_5 m 1 (v 5)).left_comm]
  rw [(c_10_5 m 1 (v 5)).left_comm]
  rw [(c_11_16 m 1 (v 16)).left_comm]
  rw [(c_10_16 m 1 (v 16)).left_comm]
  rw [(c_11_17 m 1 (v 17)).left_comm]
  rw [(c_10_17 m 1 (v 17)).left_comm]
  rw [(c_11_10 m 1 (v 10)).left_comm]
  rw [add_suffix m 10 1 (v 10),
    show 1 + (v 10) = (1 + (v 10)) by ring]
  rw [add_suffix m 11 1 (v 11),
    show 1 + (v 11) = (1 + (v 11)) by ring]

private theorem collect_right (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 1 * (X m 11 1 * (X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) =
      splitWord m ![(v 0), (v 1), (v 2), (v 3), (v 4), (v 5), (v 6), (v 7), (v 8), (v 9), (1 + (v 10)), (1 + (v 11)), (v 12), (v 13), (v 14), (v 15), (v 16), (v 17), (v 18), (v 19), (v 20), (v 21), (v 22), (v 23)] := by
  have h := (right_0 m v)
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

/-- The indicated split coordinates vanish when the literal test word commutes. -/
theorem detect_fourth (m : ℕ) (v : Fin 24 → CoefficientField m)
    (hc : Commute (splitWord m v) (rootWord m 3 1)) :
    v 0 = 0 ∧ v 18 = 0 := by
  have h : X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 10 1 * (X m 11 1 * (1)))))))))))))))))))))))))) = X m 10 1 * (X m 11 1 * (X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) := by
    simpa only [splitWord, word_3, map_one, one_mul, mul_one, xz, mul_assoc] using hc.eq
  have he := (collect_left m v).symm.trans (h.trans (collect_right m v))
  have hv := splitWord_injective m he
  constructor
  · have h := congrFun hv 9
    change ((v 0) + (v 9)) = (v 9) at h
    linear_combination h
  · have h := congrFun hv 15
    change ((v 15) + (v 18)) = (v 15) at h
    linear_combination h

end ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination
