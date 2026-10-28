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

private theorem c_2_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 4 b) :=
  xc m 2 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_2_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 5 b) :=
  xc m 2 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_2_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 11 b) :=
  xc m 2 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_2_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 16 b) :=
  xc m 2 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_2_17 (m : ℕ) (a b : CoefficientField m) :
    X m 2 a * X m 17 b = X m 17 b * X m 2 a * X m 8 (a*b) :=
  xs m 2 17 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_3_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 4 b) :=
  xc m 3 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_3_16 (m : ℕ) (a b : CoefficientField m) :
    X m 3 a * X m 16 b = X m 16 b * X m 3 a * X m 9 (a*b) :=
  xs m 3 16 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_3_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 17 b) :=
  xc m 3 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_5_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 5 a) (X m 4 b) :=
  xc m 5 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 18 b) :=
  xc m 6 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 19 b) :=
  xc m 6 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 20 b) :=
  xc m 6 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 18 b) :=
  xc m 7 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 19 b) :=
  xc m 7 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 20 b) :=
  xc m 7 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 2 b) :=
  xc m 8 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 3 b) :=
  xc m 8 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 5 b) :=
  xc m 8 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_8_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 16 b) :=
  xc m 8 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 17 b) :=
  xc m 8 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_9_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 16 b) :=
  xc m 9 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 17 b) :=
  xc m 9 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_12_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 16 b) :=
  xc m 12 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 17 b) :=
  xc m 12 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 17 b) :=
  xc m 13 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 2 b) :=
  xc m 14 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 3 b) :=
  xc m 14 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 4 b) :=
  xc m 14 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 5 b) :=
  xc m 14 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 10 b) :=
  xc m 14 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 11 b) :=
  xc m 14 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 12 b) :=
  xc m 14 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 13 b) :=
  xc m 14 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 16 b) :=
  xc m 14 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 17 b) :=
  xc m 14 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 2 b) :=
  xc m 15 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 3 b) :=
  xc m 15 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 4 b) :=
  xc m 15 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 5 b) :=
  xc m 15 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 10 b) :=
  xc m 15 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 11 b) :=
  xc m 15 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 12 b) :=
  xc m 15 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 13 b) :=
  xc m 15 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 14 b) :=
  xc m 15 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 16 b) :=
  xc m 15 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 17 b) :=
  xc m 15 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_17_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 16 b) :=
  xc m 17 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_18_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 2 b) :=
  xc m 18 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_18_3 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 3 b = X m 3 b * X m 18 a * X m 4 (a*b) :=
  xs m 18 3 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_18_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 4 b) :=
  xc m 18 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_18_5 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 5 b = X m 5 b * X m 18 a * X m 11 (a*b) * X m 9 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 18 5 11 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 11 (a*b)) (xx m 9 (a*b^2))
    (xc m 11 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem s_18_10 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 10 b = X m 10 b * X m 18 a * X m 15 (a*b) :=
  xs m 18 10 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_18_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 11 b) :=
  xc m 18 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_18_12 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 12 b = X m 12 b * X m 18 a * X m 16 (a*b) :=
  xs m 18 12 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_18_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 13 b) :=
  xc m 18 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem s_19_2 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 2 b = X m 2 b * X m 19 a * X m 5 (a*b) :=
  xs m 19 2 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_19_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 3 b) :=
  xc m 19 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_19_4 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 4 b = X m 4 b * X m 19 a * X m 8 (a*b) * X m 10 (b*a^2) := by
  simpa only [mul_comm] using xb m 4 19 8 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_19_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 5 b) :=
  xc m 19 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 10 b) :=
  xc m 19 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_19_11 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 11 b = X m 11 b * X m 19 a * X m 14 (a*b) :=
  xs m 19 11 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_19_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 12 b) :=
  xc m 19 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_19_13 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 13 b = X m 13 b * X m 19 a * X m 17 (a*b) :=
  xs m 19 13 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

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

private theorem c_20_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 12 b) :=
  xc m 20 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 13 b) :=
  xc m 20 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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
    X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (1))))))))))))))))))))) =
      X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 1 * (X m 19 1 * (X m 20 (1 + (v 20)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))) := by
  rw [(c_9_18 m (v 9) 1).left_comm]
  rw [(c_8_18 m (v 8) 1).left_comm]
  rw [(c_7_18 m (v 7) 1).left_comm]
  rw [(c_6_18 m (v 6) 1).left_comm]
  rw [(c_21_18 m (v 21) 1).left_comm]
  rw [(c_20_18 m (v 20) 1).left_comm]
  rw [(c_9_19 m (v 9) 1).left_comm]
  rw [(c_8_19 m (v 8) 1).left_comm]
  rw [(c_7_19 m (v 7) 1).left_comm]
  rw [(c_6_19 m (v 6) 1).left_comm]
  rw [(c_21_19 m (v 21) 1).left_comm]
  rw [(c_20_19 m (v 20) 1).left_comm]
  rw [(c_9_20 m (v 9) 1).left_comm]
  rw [(c_8_20 m (v 8) 1).left_comm]
  rw [(c_7_20 m (v 7) 1).left_comm]
  rw [(c_6_20 m (v 6) 1).left_comm]
  rw [(c_21_20 m (v 21) 1).left_comm]
  rw [add_suffix m 20 (v 20) 1,
    show (v 20) + 1 = (1 + (v 20)) by ring]

private theorem collect_left (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (1))))))))))))))))))))) =
      splitWord m ![0, 0, (v 2), (v 3), (v 4), (v 5), (v 6), (v 7), (v 8), (v 9), (v 10), (v 11), (v 12), (v 13), (v 14), (v 15), (v 16), (v 17), 1, 1, (1 + (v 20)), (v 21), 0, 0] := by
  have h := (left_0 m v)
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

private theorem right_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))) =
      X m 4 (v 4) * (X m 5 (v 5) * (X m 10 (v 4) * (X m 11 (v 5) * (X m 15 (v 4) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 9 ((v 5) ^ 2) * (X m 14 (v 5) * (X m 8 (v 4) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))) := by
  rw [(c_20_4 m 1 (v 4)).left_comm]
  have h1 : X m 19 1 * X m 4 (v 4) = X m 4 (v 4) * X m 19 1 * X m 8 (v 4) * X m 10 (v 4) := by
    have h := s_19_4 m 1 (v 4)
    rw [show 1 * (v 4) = (v 4) by ring, show (v 4) * 1 ^ 2 = (v 4) by ring] at h
    exact h
  rw [swap_suffix_two h1]
  rw [(c_18_4 m 1 (v 4)).left_comm]
  rw [(c_8_10 m (v 4) (v 4)).left_comm]
  rw [(c_19_10 m 1 (v 4)).left_comm]
  have h5 : X m 18 1 * X m 10 (v 4) = X m 10 (v 4) * X m 18 1 * X m 15 (v 4) := by
    have h := s_18_10 m 1 (v 4)
    rw [show 1 * (v 4) = (v 4) by ring] at h
    exact h
  rw [swap_suffix h5]
  rw [(c_18_15 m 1 (v 4)).left_comm]
  rw [(c_8_20 m (v 4) 1).left_comm]
  rw [(c_8_5 m (v 4) (v 5)).left_comm]
  have h9 : X m 20 1 * X m 5 (v 5) = X m 5 (v 5) * X m 20 1 * X m 14 (v 5) := by
    have h := s_20_5 m 1 (v 5)
    rw [show 1 * (v 5) = (v 5) by ring] at h
    exact h
  rw [swap_suffix h9]
  rw [(c_19_5 m 1 (v 5)).left_comm]
  have h11 : X m 18 1 * X m 5 (v 5) = X m 5 (v 5) * X m 18 1 * X m 11 (v 5) * X m 9 ((v 5) ^ 2) := by
    have h := s_18_5 m 1 (v 5)
    rw [show 1 * (v 5) = (v 5) by ring, show 1 * (v 5) ^ 2 = ((v 5) ^ 2) by ring] at h
    exact h
  rw [swap_suffix_two h11]
  rw [(c_15_5 m (v 4) (v 5)).left_comm]
  rw [(c_10_5 m (v 4) (v 5)).left_comm]
  rw [(c_18_11 m 1 (v 5)).left_comm]
  rw [(c_15_11 m (v 4) (v 5)).left_comm]
  rw [(c_9_19 m ((v 5) ^ 2) 1).left_comm]
  rw [(c_9_20 m ((v 5) ^ 2) 1).left_comm]

private theorem right_1 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 10 (v 4) * (X m 11 (v 5) * (X m 15 (v 4) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 9 ((v 5) ^ 2) * (X m 14 (v 5) * (X m 8 (v 4) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))) =
      X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 10 (v 4) * (X m 11 (v 5) * (X m 14 (v 5) * (X m 15 (v 4) * (X m 18 1 * (X m 19 1 * (X m 17 (v 17) * (X m 20 1 * (X m 8 (v 4) * (X m 9 ((v 5) ^ 2) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))) := by
  rw [(c_9_14 m ((v 5) ^ 2) (v 5)).left_comm]
  rw [(c_20_14 m 1 (v 5)).left_comm]
  rw [(c_19_14 m 1 (v 5)).left_comm]
  rw [(c_18_14 m 1 (v 5)).left_comm]
  rw [(c_15_14 m (v 4) (v 5)).left_comm]
  rw [(c_9_8 m ((v 5) ^ 2) (v 4)).left_comm]
  rw [(c_9_16 m ((v 5) ^ 2) (v 16)).left_comm]
  rw [(c_8_16 m (v 4) (v 16)).left_comm]
  rw [(c_20_16 m 1 (v 16)).left_comm]
  rw [(c_19_16 m 1 (v 16)).left_comm]
  rw [(c_18_16 m 1 (v 16)).left_comm]
  rw [(c_15_16 m (v 4) (v 16)).left_comm]
  rw [(c_14_16 m (v 5) (v 16)).left_comm]
  rw [(c_11_16 m (v 5) (v 16)).left_comm]
  rw [(c_10_16 m (v 4) (v 16)).left_comm]
  rw [(c_9_17 m ((v 5) ^ 2) (v 17)).left_comm]
  rw [(c_8_17 m (v 4) (v 17)).left_comm]
  rw [(c_20_17 m 1 (v 17)).left_comm]

private theorem right_2 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 10 (v 4) * (X m 11 (v 5) * (X m 14 (v 5) * (X m 15 (v 4) * (X m 18 1 * (X m 19 1 * (X m 17 (v 17) * (X m 20 1 * (X m 8 (v 4) * (X m 9 ((v 5) ^ 2) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))) =
      X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 (v 5) * (X m 14 (v 5) * (X m 15 ((v 10) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 8 (v 4) * (X m 11 (v 11) * (X m 9 ((v 5) ^ 2) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) := by
  rw [(c_19_17 m 1 (v 17)).left_comm]
  rw [(c_18_17 m 1 (v 17)).left_comm]
  rw [(c_15_17 m (v 4) (v 17)).left_comm]
  rw [(c_14_17 m (v 5) (v 17)).left_comm]
  rw [(c_11_17 m (v 5) (v 17)).left_comm]
  rw [(c_10_17 m (v 4) (v 17)).left_comm]
  rw [(c_9_10 m ((v 5) ^ 2) (v 10)).left_comm]
  rw [(c_8_10 m (v 4) (v 10)).left_comm]
  rw [(c_20_10 m 1 (v 10)).left_comm]
  rw [(c_19_10 m 1 (v 10)).left_comm]
  have h10 : X m 18 1 * X m 10 (v 10) = X m 10 (v 10) * X m 18 1 * X m 15 (v 10) := by
    have h := s_18_10 m 1 (v 10)
    rw [show 1 * (v 10) = (v 10) by ring] at h
    exact h
  rw [swap_suffix h10]
  rw [(c_15_10 m (v 4) (v 10)).left_comm]
  rw [(c_14_10 m (v 5) (v 10)).left_comm]
  rw [(c_11_10 m (v 5) (v 10)).left_comm]
  rw [add_suffix m 10 (v 4) (v 10),
    show (v 4) + (v 10) = ((v 10) + (v 4)) by ring]
  rw [(c_18_15 m 1 (v 10)).left_comm]
  rw [add_suffix m 15 (v 4) (v 10),
    show (v 4) + (v 10) = ((v 10) + (v 4)) by ring]
  rw [(c_9_11 m ((v 5) ^ 2) (v 11)).left_comm]

private theorem right_3 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 (v 5) * (X m 14 (v 5) * (X m 15 ((v 10) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 8 (v 4) * (X m 11 (v 11) * (X m 9 ((v 5) ^ 2) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) =
      X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 14 ((v 11) + (v 5)) * (X m 15 ((v 10) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 5 (v 2) * (X m 20 1 * (X m 11 (v 2) * (X m 8 (v 4) * (X m 9 ((v 5) ^ 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))) := by
  rw [(c_8_11 m (v 4) (v 11)).left_comm]
  rw [(c_20_11 m 1 (v 11)).left_comm]
  have h2 : X m 19 1 * X m 11 (v 11) = X m 11 (v 11) * X m 19 1 * X m 14 (v 11) := by
    have h := s_19_11 m 1 (v 11)
    rw [show 1 * (v 11) = (v 11) by ring] at h
    exact h
  rw [swap_suffix h2]
  rw [(c_18_11 m 1 (v 11)).left_comm]
  rw [(c_15_11 m ((v 10) + (v 4)) (v 11)).left_comm]
  rw [(c_14_11 m (v 5) (v 11)).left_comm]
  rw [add_suffix m 11 (v 5) (v 11),
    show (v 5) + (v 11) = ((v 11) + (v 5)) by ring]
  rw [(c_19_14 m 1 (v 11)).left_comm]
  rw [(c_18_14 m 1 (v 11)).left_comm]
  rw [(c_15_14 m ((v 10) + (v 4)) (v 11)).left_comm]
  rw [add_suffix m 14 (v 5) (v 11),
    show (v 5) + (v 11) = ((v 11) + (v 5)) by ring]
  rw [(c_9_2 m ((v 5) ^ 2) (v 2)).left_comm]
  rw [(c_8_2 m (v 4) (v 2)).left_comm]
  have h13 : X m 20 1 * X m 2 (v 2) = X m 2 (v 2) * X m 20 1 * X m 11 (v 2) := by
    have h := s_20_2 m 1 (v 2)
    rw [show 1 * (v 2) = (v 2) by ring] at h
    exact h
  rw [swap_suffix h13]
  have h14 : X m 19 1 * X m 2 (v 2) = X m 2 (v 2) * X m 19 1 * X m 5 (v 2) := by
    have h := s_19_2 m 1 (v 2)
    rw [show 1 * (v 2) = (v 2) by ring] at h
    exact h
  rw [swap_suffix h14]
  rw [(c_18_2 m 1 (v 2)).left_comm]
  rw [(c_15_2 m ((v 10) + (v 4)) (v 2)).left_comm]
  rw [(c_14_2 m ((v 11) + (v 5)) (v 2)).left_comm]

private theorem right_4 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 14 ((v 11) + (v 5)) * (X m 15 ((v 10) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 5 (v 2) * (X m 20 1 * (X m 11 (v 2) * (X m 8 (v 4) * (X m 9 ((v 5) ^ 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))) =
      X m 4 (v 4) * (X m 5 ((v 2) + (v 5)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 2) + (v 5)) * (X m 2 (v 2) * (X m 14 ((v 11) + (v 5)) * (X m 15 ((v 10) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 11 (v 2) * (X m 9 ((v 2) ^ 2) * (X m 8 (v 4) * (X m 9 ((v 5) ^ 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))) := by
  rw [(c_19_5 m 1 (v 2)).left_comm]
  have h1 : X m 18 1 * X m 5 (v 2) = X m 5 (v 2) * X m 18 1 * X m 11 (v 2) * X m 9 ((v 2) ^ 2) := by
    have h := s_18_5 m 1 (v 2)
    rw [show 1 * (v 2) = (v 2) by ring, show 1 * (v 2) ^ 2 = ((v 2) ^ 2) by ring] at h
    exact h
  rw [swap_suffix_two h1]
  rw [(c_15_5 m ((v 10) + (v 4)) (v 2)).left_comm]
  rw [(c_14_5 m ((v 11) + (v 5)) (v 2)).left_comm]
  rw [(c_2_5 m (v 2) (v 2)).left_comm]
  rw [(c_11_5 m ((v 11) + (v 5)) (v 2)).left_comm]
  rw [(c_10_5 m ((v 10) + (v 4)) (v 2)).left_comm]
  rw [(c_17_5 m (v 17) (v 2)).left_comm]
  rw [(c_16_5 m (v 16) (v 2)).left_comm]
  rw [add_suffix m 5 (v 5) (v 2),
    show (v 5) + (v 2) = ((v 2) + (v 5)) by ring]
  rw [(c_18_11 m 1 (v 2)).left_comm]
  rw [(c_15_11 m ((v 10) + (v 4)) (v 2)).left_comm]
  rw [(c_14_11 m ((v 11) + (v 5)) (v 2)).left_comm]
  rw [(c_2_11 m (v 2) (v 2)).left_comm]
  rw [add_suffix m 11 ((v 11) + (v 5)) (v 2),
    show ((v 11) + (v 5)) + (v 2) = ((v 11) + (v 2) + (v 5)) by ring]
  rw [(c_9_19 m ((v 2) ^ 2) 1).left_comm]
  rw [(c_9_20 m ((v 2) ^ 2) 1).left_comm]
  rw [(c_9_11 m ((v 2) ^ 2) (v 2)).left_comm]

private theorem right_5 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 ((v 2) + (v 5)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 2) + (v 5)) * (X m 2 (v 2) * (X m 14 ((v 11) + (v 5)) * (X m 15 ((v 10) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 11 (v 2) * (X m 9 ((v 2) ^ 2) * (X m 8 (v 4) * (X m 9 ((v 5) ^ 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))) =
      X m 4 (v 4) * (X m 5 ((v 2) + (v 5)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 14 ((v 11) + (v 2) + (v 5)) * (X m 15 ((v 10) + (v 4)) * (X m 3 (v 3) * (X m 18 1 * (X m 4 (v 3) * (X m 19 1 * (X m 20 1 * (X m 8 (v 3) * (X m 15 (v 3) * (X m 8 (v 4) * (X m 9 (((v 2) ^ 2) + ((v 5) ^ 2)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))) := by
  rw [(c_20_11 m 1 (v 2)).left_comm]
  have h1 : X m 19 1 * X m 11 (v 2) = X m 11 (v 2) * X m 19 1 * X m 14 (v 2) := by
    have h := s_19_11 m 1 (v 2)
    rw [show 1 * (v 2) = (v 2) by ring] at h
    exact h
  rw [swap_suffix h1]
  rw [(c_18_11 m 1 (v 2)).left_comm]
  rw [(c_15_11 m ((v 10) + (v 4)) (v 2)).left_comm]
  rw [(c_14_11 m ((v 11) + (v 5)) (v 2)).left_comm]
  rw [(c_2_11 m (v 2) (v 2)).left_comm]
  rw [add_suffix m 11 ((v 11) + (v 2) + (v 5)) (v 2),
    show ((v 11) + (v 2) + (v 5)) + (v 2) = ((v 11) + (v 5)) by ring_nf; simp only [CharTwo.two_eq_zero, mul_zero, add_zero]]
  rw [(c_19_14 m 1 (v 2)).left_comm]
  rw [(c_18_14 m 1 (v 2)).left_comm]
  rw [(c_15_14 m ((v 10) + (v 4)) (v 2)).left_comm]
  rw [add_suffix m 14 ((v 11) + (v 5)) (v 2),
    show ((v 11) + (v 5)) + (v 2) = ((v 11) + (v 2) + (v 5)) by ring]
  rw [(c_9_8 m ((v 2) ^ 2) (v 4)).left_comm]
  rw [add_suffix m 9 ((v 2) ^ 2) ((v 5) ^ 2),
    show ((v 2) ^ 2) + ((v 5) ^ 2) = (((v 2) ^ 2) + ((v 5) ^ 2)) by ring]
  rw [(c_9_3 m (((v 2) ^ 2) + ((v 5) ^ 2)) (v 3)).left_comm]
  rw [(c_8_3 m (v 4) (v 3)).left_comm]
  have h15 : X m 20 1 * X m 3 (v 3) = X m 3 (v 3) * X m 20 1 * X m 8 (v 3) * X m 15 (v 3) := by
    have h := s_20_3 m 1 (v 3)
    rw [show 1 * (v 3) = (v 3) by ring, show (v 3) * 1 ^ 2 = (v 3) by ring] at h
    exact h
  rw [swap_suffix_two h15]
  rw [(c_19_3 m 1 (v 3)).left_comm]
  have h17 : X m 18 1 * X m 3 (v 3) = X m 3 (v 3) * X m 18 1 * X m 4 (v 3) := by
    have h := s_18_3 m 1 (v 3)
    rw [show 1 * (v 3) = (v 3) by ring] at h
    exact h
  rw [swap_suffix h17]

private theorem right_6 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 ((v 2) + (v 5)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 14 ((v 11) + (v 2) + (v 5)) * (X m 15 ((v 10) + (v 4)) * (X m 3 (v 3) * (X m 18 1 * (X m 4 (v 3) * (X m 19 1 * (X m 20 1 * (X m 8 (v 3) * (X m 15 (v 3) * (X m 8 (v 4) * (X m 9 (((v 2) ^ 2) + ((v 5) ^ 2)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))) =
      X m 4 ((v 3) + (v 4)) * (X m 5 ((v 2) + (v 5)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 14 ((v 11) + (v 2) + (v 5)) * (X m 15 ((v 10) + (v 3) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 8 (v 3) * (X m 8 (v 4) * (X m 9 (((v 2) ^ 2) + ((v 5) ^ 2)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) := by
  rw [(c_15_3 m ((v 10) + (v 4)) (v 3)).left_comm]
  rw [(c_14_3 m ((v 11) + (v 2) + (v 5)) (v 3)).left_comm]
  rw [(c_18_4 m 1 (v 3)).left_comm]
  rw [(c_15_4 m ((v 10) + (v 4)) (v 3)).left_comm]
  rw [(c_14_4 m ((v 11) + (v 2) + (v 5)) (v 3)).left_comm]
  rw [(c_3_4 m (v 3) (v 3)).left_comm]
  rw [(c_2_4 m (v 2) (v 3)).left_comm]
  rw [(c_11_4 m ((v 11) + (v 5)) (v 3)).left_comm]
  rw [(c_10_4 m ((v 10) + (v 4)) (v 3)).left_comm]
  rw [(c_17_4 m (v 17) (v 3)).left_comm]
  rw [(c_16_4 m (v 16) (v 3)).left_comm]
  rw [(c_5_4 m ((v 2) + (v 5)) (v 3)).left_comm]
  rw [add_suffix m 4 (v 4) (v 3),
    show (v 4) + (v 3) = ((v 3) + (v 4)) by ring]
  rw [(c_8_15 m (v 3) (v 3)).left_comm]
  rw [(c_20_15 m 1 (v 3)).left_comm]
  rw [(c_19_15 m 1 (v 3)).left_comm]
  rw [(c_18_15 m 1 (v 3)).left_comm]
  rw [add_suffix m 15 ((v 10) + (v 4)) (v 3),
    show ((v 10) + (v 4)) + (v 3) = ((v 10) + (v 3) + (v 4)) by ring]

private theorem right_7 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 3) + (v 4)) * (X m 5 ((v 2) + (v 5)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 14 ((v 11) + (v 2) + (v 5)) * (X m 15 ((v 10) + (v 3) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 8 (v 3) * (X m 8 (v 4) * (X m 9 (((v 2) ^ 2) + ((v 5) ^ 2)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) =
      X m 4 ((v 3) + (v 4)) * (X m 5 ((v 2) + (v 5)) * (X m 16 ((v 12) + (v 16)) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 9 ((v 12) * (v 3)) * (X m 12 (v 12) * (X m 14 ((v 11) + (v 2) + (v 5)) * (X m 15 ((v 10) + (v 3) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 8 ((v 3) + (v 4)) * (X m 9 (((v 2) ^ 2) + ((v 5) ^ 2)) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) := by
  rw [add_suffix m 8 (v 3) (v 4),
    show (v 3) + (v 4) = ((v 3) + (v 4)) by ring]
  rw [(c_9_12 m (((v 2) ^ 2) + ((v 5) ^ 2)) (v 12)).left_comm]
  rw [(c_8_12 m ((v 3) + (v 4)) (v 12)).left_comm]
  rw [(c_20_12 m 1 (v 12)).left_comm]
  rw [(c_19_12 m 1 (v 12)).left_comm]
  have h5 : X m 18 1 * X m 12 (v 12) = X m 12 (v 12) * X m 18 1 * X m 16 (v 12) := by
    have h := s_18_12 m 1 (v 12)
    rw [show 1 * (v 12) = (v 12) by ring] at h
    exact h
  rw [swap_suffix h5]
  rw [(c_15_12 m ((v 10) + (v 3) + (v 4)) (v 12)).left_comm]
  rw [(c_14_12 m ((v 11) + (v 2) + (v 5)) (v 12)).left_comm]
  rw [(c_18_16 m 1 (v 12)).left_comm]
  rw [(c_15_16 m ((v 10) + (v 3) + (v 4)) (v 12)).left_comm]
  rw [(c_14_16 m ((v 11) + (v 2) + (v 5)) (v 12)).left_comm]
  rw [(c_12_16 m (v 12) (v 12)).left_comm]
  have h12 : X m 3 (v 3) * X m 16 (v 12) = X m 16 (v 12) * X m 3 (v 3) * X m 9 ((v 12) * (v 3)) := by
    have h := s_3_16 m (v 3) (v 12)
    rw [show (v 3) * (v 12) = ((v 12) * (v 3)) by ring] at h
    exact h
  rw [swap_suffix h12]
  rw [(c_2_16 m (v 2) (v 12)).left_comm]
  rw [(c_11_16 m ((v 11) + (v 5)) (v 12)).left_comm]
  rw [(c_10_16 m ((v 10) + (v 4)) (v 12)).left_comm]
  rw [(c_17_16 m (v 17) (v 12)).left_comm]
  rw [add_suffix m 16 (v 16) (v 12),
    show (v 16) + (v 12) = ((v 12) + (v 16)) by ring]

private theorem right_8 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 3) + (v 4)) * (X m 5 ((v 2) + (v 5)) * (X m 16 ((v 12) + (v 16)) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 9 ((v 12) * (v 3)) * (X m 12 (v 12) * (X m 14 ((v 11) + (v 2) + (v 5)) * (X m 15 ((v 10) + (v 3) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 8 ((v 3) + (v 4)) * (X m 9 (((v 2) ^ 2) + ((v 5) ^ 2)) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) =
      X m 4 ((v 3) + (v 4)) * (X m 5 ((v 2) + (v 5)) * (X m 16 ((v 12) + (v 16)) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 11) + (v 2) + (v 5)) * (X m 17 (v 13) * (X m 15 ((v 10) + (v 3) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 8 ((v 3) + (v 4)) * (X m 9 (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) := by
  rw [(c_9_12 m ((v 12) * (v 3)) (v 12)).left_comm]
  rw [(c_9_14 m ((v 12) * (v 3)) ((v 11) + (v 2) + (v 5))).left_comm]
  rw [(c_9_15 m ((v 12) * (v 3)) ((v 10) + (v 3) + (v 4))).left_comm]
  rw [(c_9_18 m ((v 12) * (v 3)) 1).left_comm]
  rw [(c_9_19 m ((v 12) * (v 3)) 1).left_comm]
  rw [(c_9_20 m ((v 12) * (v 3)) 1).left_comm]
  rw [(c_9_8 m ((v 12) * (v 3)) ((v 3) + (v 4))).left_comm]
  rw [add_suffix m 9 ((v 12) * (v 3)) (((v 2) ^ 2) + ((v 5) ^ 2)),
    show ((v 12) * (v 3)) + (((v 2) ^ 2) + ((v 5) ^ 2)) = (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) by ring]
  rw [(c_9_13 m (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) (v 13)).left_comm]
  rw [(c_8_13 m ((v 3) + (v 4)) (v 13)).left_comm]
  rw [(c_20_13 m 1 (v 13)).left_comm]
  have h11 : X m 19 1 * X m 13 (v 13) = X m 13 (v 13) * X m 19 1 * X m 17 (v 13) := by
    have h := s_19_13 m 1 (v 13)
    rw [show 1 * (v 13) = (v 13) by ring] at h
    exact h
  rw [swap_suffix h11]
  rw [(c_18_13 m 1 (v 13)).left_comm]
  rw [(c_15_13 m ((v 10) + (v 3) + (v 4)) (v 13)).left_comm]
  rw [(c_14_13 m ((v 11) + (v 2) + (v 5)) (v 13)).left_comm]
  rw [(c_19_17 m 1 (v 13)).left_comm]
  rw [(c_18_17 m 1 (v 13)).left_comm]
  rw [(c_15_17 m ((v 10) + (v 3) + (v 4)) (v 13)).left_comm]

private theorem right_9 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 3) + (v 4)) * (X m 5 ((v 2) + (v 5)) * (X m 16 ((v 12) + (v 16)) * (X m 17 (v 17) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 11) + (v 2) + (v 5)) * (X m 17 (v 13) * (X m 15 ((v 10) + (v 3) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 8 ((v 3) + (v 4)) * (X m 9 (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) =
      X m 4 ((v 3) + (v 4)) * (X m 5 ((v 2) + (v 5)) * (X m 16 ((v 12) + (v 16)) * (X m 17 ((v 13) + (v 17)) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 11) + (v 2) + (v 5)) * (X m 15 ((v 10) + (v 3) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 8 ((v 3) + (v 4) + ((v 13) * (v 2))) * (X m 14 (v 14) * (X m 9 (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))) := by
  rw [(c_14_17 m ((v 11) + (v 2) + (v 5)) (v 13)).left_comm]
  rw [(c_13_17 m (v 13) (v 13)).left_comm]
  rw [(c_12_17 m (v 12) (v 13)).left_comm]
  rw [(c_3_17 m (v 3) (v 13)).left_comm]
  have h4 : X m 2 (v 2) * X m 17 (v 13) = X m 17 (v 13) * X m 2 (v 2) * X m 8 ((v 13) * (v 2)) := by
    have h := s_2_17 m (v 2) (v 13)
    rw [show (v 2) * (v 13) = ((v 13) * (v 2)) by ring] at h
    exact h
  rw [swap_suffix h4]
  rw [(c_11_17 m ((v 11) + (v 5)) (v 13)).left_comm]
  rw [(c_10_17 m ((v 10) + (v 4)) (v 13)).left_comm]
  rw [add_suffix m 17 (v 17) (v 13),
    show (v 17) + (v 13) = ((v 13) + (v 17)) by ring]
  rw [(c_8_3 m ((v 13) * (v 2)) (v 3)).left_comm]
  rw [(c_8_12 m ((v 13) * (v 2)) (v 12)).left_comm]
  rw [(c_8_13 m ((v 13) * (v 2)) (v 13)).left_comm]
  rw [(c_8_14 m ((v 13) * (v 2)) ((v 11) + (v 2) + (v 5))).left_comm]
  rw [(c_8_15 m ((v 13) * (v 2)) ((v 10) + (v 3) + (v 4))).left_comm]
  rw [(c_8_18 m ((v 13) * (v 2)) 1).left_comm]
  rw [(c_8_19 m ((v 13) * (v 2)) 1).left_comm]
  rw [(c_8_20 m ((v 13) * (v 2)) 1).left_comm]
  rw [add_suffix m 8 ((v 13) * (v 2)) ((v 3) + (v 4)),
    show ((v 13) * (v 2)) + ((v 3) + (v 4)) = ((v 3) + (v 4) + ((v 13) * (v 2))) by ring]
  rw [(c_9_14 m (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) (v 14)).left_comm]

private theorem right_10 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 3) + (v 4)) * (X m 5 ((v 2) + (v 5)) * (X m 16 ((v 12) + (v 16)) * (X m 17 ((v 13) + (v 17)) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 11) + (v 2) + (v 5)) * (X m 15 ((v 10) + (v 3) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 8 ((v 3) + (v 4) + ((v 13) * (v 2))) * (X m 14 (v 14) * (X m 9 (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))) =
      X m 4 ((v 3) + (v 4)) * (X m 5 ((v 2) + (v 5)) * (X m 16 ((v 12) + (v 16)) * (X m 17 ((v 13) + (v 17)) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 11) + (v 14) + (v 2) + (v 5)) * (X m 15 ((v 10) + (v 15) + (v 3) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 (1 + (v 20)) * (X m 21 (v 21) * (X m 8 ((v 3) + (v 4) + ((v 13) * (v 2))) * (X m 6 (v 6) * (X m 9 (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))) := by
  rw [(c_8_14 m ((v 3) + (v 4) + ((v 13) * (v 2))) (v 14)).left_comm]
  rw [(c_20_14 m 1 (v 14)).left_comm]
  rw [(c_19_14 m 1 (v 14)).left_comm]
  rw [(c_18_14 m 1 (v 14)).left_comm]
  rw [(c_15_14 m ((v 10) + (v 3) + (v 4)) (v 14)).left_comm]
  rw [add_suffix m 14 ((v 11) + (v 2) + (v 5)) (v 14),
    show ((v 11) + (v 2) + (v 5)) + (v 14) = ((v 11) + (v 14) + (v 2) + (v 5)) by ring]
  rw [(c_9_15 m (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) (v 15)).left_comm]
  rw [(c_8_15 m ((v 3) + (v 4) + ((v 13) * (v 2))) (v 15)).left_comm]
  rw [(c_20_15 m 1 (v 15)).left_comm]
  rw [(c_19_15 m 1 (v 15)).left_comm]
  rw [(c_18_15 m 1 (v 15)).left_comm]
  rw [add_suffix m 15 ((v 10) + (v 3) + (v 4)) (v 15),
    show ((v 10) + (v 3) + (v 4)) + (v 15) = ((v 10) + (v 15) + (v 3) + (v 4)) by ring]
  rw [(c_9_20 m (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) (v 20)).left_comm]
  rw [(c_8_20 m ((v 3) + (v 4) + ((v 13) * (v 2))) (v 20)).left_comm]
  rw [add_suffix m 20 1 (v 20),
    show 1 + (v 20) = (1 + (v 20)) by ring]
  rw [(c_9_21 m (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) (v 21)).left_comm]
  rw [(c_8_21 m ((v 3) + (v 4) + ((v 13) * (v 2))) (v 21)).left_comm]
  rw [(c_9_6 m (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) (v 6)).left_comm]

private theorem right_11 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 3) + (v 4)) * (X m 5 ((v 2) + (v 5)) * (X m 16 ((v 12) + (v 16)) * (X m 17 ((v 13) + (v 17)) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 11) + (v 14) + (v 2) + (v 5)) * (X m 15 ((v 10) + (v 15) + (v 3) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 (1 + (v 20)) * (X m 21 (v 21) * (X m 8 ((v 3) + (v 4) + ((v 13) * (v 2))) * (X m 6 (v 6) * (X m 9 (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))) =
      X m 4 ((v 3) + (v 4)) * (X m 5 ((v 2) + (v 5)) * (X m 16 ((v 12) + (v 16)) * (X m 17 ((v 13) + (v 17)) * (X m 10 ((v 10) + (v 4)) * (X m 11 ((v 11) + (v 5)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 11) + (v 14) + (v 2) + (v 5)) * (X m 15 ((v 10) + (v 15) + (v 3) + (v 4)) * (X m 18 1 * (X m 19 1 * (X m 20 (1 + (v 20)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 3) + (v 4) + (v 8) + ((v 13) * (v 2))) * (X m 9 ((v 9) + ((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) * (1)))))))))))))))))))) := by
  rw [(c_8_6 m ((v 3) + (v 4) + ((v 13) * (v 2))) (v 6)).left_comm]
  rw [(c_9_7 m (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) (v 7)).left_comm]
  rw [(c_8_7 m ((v 3) + (v 4) + ((v 13) * (v 2))) (v 7)).left_comm]
  rw [(c_9_8 m (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) (v 8)).left_comm]
  rw [add_suffix m 8 ((v 3) + (v 4) + ((v 13) * (v 2))) (v 8),
    show ((v 3) + (v 4) + ((v 13) * (v 2))) + (v 8) = ((v 3) + (v 4) + (v 8) + ((v 13) * (v 2))) by ring]
  rw [add_suffix m 9 (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) (v 9),
    show (((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) + (v 9) = ((v 9) + ((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))) by ring]

private theorem collect_right (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))) =
      splitWord m ![0, 0, (v 2), (v 3), ((v 3) + (v 4)), ((v 2) + (v 5)), (v 6), (v 7), ((v 3) + (v 4) + (v 8) + ((v 13) * (v 2))), ((v 9) + ((v 2) ^ 2) + ((v 5) ^ 2) + ((v 12) * (v 3))), ((v 10) + (v 4)), ((v 11) + (v 5)), (v 12), (v 13), ((v 11) + (v 14) + (v 2) + (v 5)), ((v 10) + (v 15) + (v 3) + (v 4)), ((v 12) + (v 16)), ((v 13) + (v 17)), 1, 1, (1 + (v 20)), (v 21), 0, 0] := by
  have h := (right_0 m v).trans ((right_1 m v).trans ((right_2 m v).trans ((right_3 m v).trans ((right_4 m v).trans ((right_5 m v).trans ((right_6 m v).trans ((right_7 m v).trans ((right_8 m v).trans ((right_9 m v).trans ((right_10 m v).trans ((right_11 m v))))))))))))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

/-- The indicated split coordinates vanish when the literal test word commutes. -/
theorem detect_seventh (m : ℕ) (v : Fin 24 → CoefficientField m)
    (h0 : v 0 = 0)
    (h1 : v 1 = 0)
    (h18 : v 18 = 0)
    (h19 : v 19 = 0)
    (h22 : v 22 = 0)
    (h23 : v 23 = 0)
    (hc : Commute (splitWord m v) (rootWord m 6 1)) :
    v 4 = 0 ∧ v 3 = 0 := by
  have h : X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 18 1 * (X m 19 1 * (X m 20 1 * (1))))))))))))))))))))) = X m 18 1 * (X m 19 1 * (X m 20 1 * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))) := by
    simpa only [splitWord, word_6, map_one, one_mul, mul_one, h0, h1, h18, h19, h22, h23 , xz, mul_assoc] using hc.eq
  have he := (collect_left m v).symm.trans (h.trans (collect_right m v))
  have hv := splitWord_injective m he
  constructor
  · have h := congrFun hv 10
    change (v 10) = ((v 10) + (v 4)) at h
    linear_combination -h
  · have h := congrFun hv 4
    change (v 4) = ((v 3) + (v 4)) at h
    linear_combination -h

end ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination
