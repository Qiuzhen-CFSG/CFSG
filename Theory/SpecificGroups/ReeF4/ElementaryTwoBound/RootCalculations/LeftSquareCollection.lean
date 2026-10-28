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
namespace ReeF4.ElementaryTwoBound.RootCalculations.LeftSquareCollection
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

private theorem c_2_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 10 b) :=
  xc m 2 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_2_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 11 b) :=
  xc m 2 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_3_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 2 b) :=
  xc m 3 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_3_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 4 b) :=
  xc m 3 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_3_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 5 b) :=
  xc m 3 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_3_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 10 b) :=
  xc m 3 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_3_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 11 b) :=
  xc m 3 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_5_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 5 a) (X m 4 b) :=
  xc m 5 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 2 b) :=
  xc m 6 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 3 b) :=
  xc m 6 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 4 b) :=
  xc m 6 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 5 b) :=
  xc m 6 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 10 b) :=
  xc m 6 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 11 b) :=
  xc m 6 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_6_12 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 12 b = X m 12 b * X m 6 a * X m 10 (a*b) :=
  xs m 6 12 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_6_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 13 b) :=
  xc m 6 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 14 b) :=
  xc m 6 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 15 b) :=
  xc m 6 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 2 b) :=
  xc m 7 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 3 b) :=
  xc m 7 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 4 b) :=
  xc m 7 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 5 b) :=
  xc m 7 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_7_6 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 6 b = X m 6 b * X m 7 a * X m 8 (a*b) * X m 9 (b*a^2) := by
  simpa only [mul_comm] using xb m 6 7 8 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_7_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 10 b) :=
  xc m 7 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 11 b) :=
  xc m 7 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 12 b) :=
  xc m 7 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_7_13 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 13 b = X m 13 b * X m 7 a * X m 11 (a*b) :=
  xs m 7 13 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_7_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 14 b) :=
  xc m 7 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 15 b) :=
  xc m 7 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 2 b) :=
  xc m 8 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 3 b) :=
  xc m 8 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_9_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 2 b) :=
  xc m 9 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 3 b) :=
  xc m 9 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_11_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 10 b) :=
  xc m 11 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 2 b) :=
  xc m 12 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 3 b) :=
  xc m 12 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_12_4 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 4 b = X m 4 b * X m 12 a * X m 9 (a*b) :=
  xs m 12 4 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_12_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 5 b) :=
  xc m 12 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 10 b) :=
  xc m 12 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 11 b) :=
  xc m 12 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 2 b) :=
  xc m 13 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 3 b) :=
  xc m 13 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 4 b) :=
  xc m 13 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_13_5 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 5 b = X m 5 b * X m 13 a * X m 8 (a*b) :=
  xs m 13 5 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_13_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 10 b) :=
  xc m 13 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 11 b) :=
  xc m 13 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_13_12 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 12 b = X m 12 b * X m 13 a * X m 14 (a*b) * X m 15 (b*a^2) := by
  simpa only [mul_comm] using xb m 12 13 14 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

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

private theorem chunk_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))) =
      X m 5 (v 5) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 9 ((v 12) * (v 4)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))) := by
  rw [(c_9_4 m (v 9) (v 4)).left_comm]
  rw [(c_8_4 m (v 8) (v 4)).left_comm]
  rw [(c_7_4 m (v 7) (v 4)).left_comm]
  rw [(c_6_4 m (v 6) (v 4)).left_comm]
  rw [(c_15_4 m (v 15) (v 4)).left_comm]
  rw [(c_14_4 m (v 14) (v 4)).left_comm]
  rw [(c_13_4 m (v 13) (v 4)).left_comm]
  have h7 : X m 12 (v 12) * X m 4 (v 4) = X m 4 (v 4) * X m 12 (v 12) * X m 9 ((v 12) * (v 4)) := by
    have h := s_12_4 m (v 12) (v 4)
    rw [show (v 12) * (v 4) = ((v 12) * (v 4)) by ring] at h
    exact h
  rw [swap_suffix h7]
  rw [(c_3_4 m (v 3) (v 4)).left_comm]
  rw [(c_2_4 m (v 2) (v 4)).left_comm]
  rw [(c_11_4 m (v 11) (v 4)).left_comm]
  rw [(c_10_4 m (v 10) (v 4)).left_comm]
  rw [(c_5_4 m (v 5) (v 4)).left_comm]
  rw [add_suffix m 4 (v 4) (v 4),
    show (v 4) + (v 4) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_13 m ((v 12) * (v 4)) (v 13)).left_comm]
  rw [(c_9_14 m ((v 12) * (v 4)) (v 14)).left_comm]
  rw [(c_9_15 m ((v 12) * (v 4)) (v 15)).left_comm]
  rw [(c_9_6 m ((v 12) * (v 4)) (v 6)).left_comm]

private theorem chunk_1 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 5 (v 5) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 9 ((v 12) * (v 4)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))) =
      X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 8 ((v 13) * (v 5)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + ((v 12) * (v 4))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))) := by
  rw [(c_9_7 m ((v 12) * (v 4)) (v 7)).left_comm]
  rw [(c_9_8 m ((v 12) * (v 4)) (v 8)).left_comm]
  rw [add_suffix m 9 ((v 12) * (v 4)) (v 9),
    show ((v 12) * (v 4)) + (v 9) = ((v 9) + ((v 12) * (v 4))) by ring]
  rw [(c_9_5 m ((v 9) + ((v 12) * (v 4))) (v 5)).left_comm]
  rw [(c_8_5 m (v 8) (v 5)).left_comm]
  rw [(c_7_5 m (v 7) (v 5)).left_comm]
  rw [(c_6_5 m (v 6) (v 5)).left_comm]
  rw [(c_15_5 m (v 15) (v 5)).left_comm]
  rw [(c_14_5 m (v 14) (v 5)).left_comm]
  have h9 : X m 13 (v 13) * X m 5 (v 5) = X m 5 (v 5) * X m 13 (v 13) * X m 8 ((v 13) * (v 5)) := by
    have h := s_13_5 m (v 13) (v 5)
    rw [show (v 13) * (v 5) = ((v 13) * (v 5)) by ring] at h
    exact h
  rw [swap_suffix h9]
  rw [(c_12_5 m (v 12) (v 5)).left_comm]
  rw [(c_3_5 m (v 3) (v 5)).left_comm]
  rw [(c_2_5 m (v 2) (v 5)).left_comm]
  rw [(c_11_5 m (v 11) (v 5)).left_comm]
  rw [(c_10_5 m (v 10) (v 5)).left_comm]
  rw [add_suffix m 5 (v 5) (v 5),
    show (v 5) + (v 5) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_8_14 m ((v 13) * (v 5)) (v 14)).left_comm]
  rw [(c_8_15 m ((v 13) * (v 5)) (v 15)).left_comm]

private theorem chunk_2 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 8 ((v 13) * (v 5)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + ((v 12) * (v 4))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))) =
      X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 11 (v 11) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))) := by
  rw [(c_8_6 m ((v 13) * (v 5)) (v 6)).left_comm]
  rw [(c_8_7 m ((v 13) * (v 5)) (v 7)).left_comm]
  rw [add_suffix m 8 ((v 13) * (v 5)) (v 8),
    show ((v 13) * (v 5)) + (v 8) = ((v 8) + ((v 13) * (v 5))) by ring]
  rw [(c_9_10 m ((v 9) + ((v 12) * (v 4))) (v 10)).left_comm]
  rw [(c_8_10 m ((v 8) + ((v 13) * (v 5))) (v 10)).left_comm]
  rw [(c_7_10 m (v 7) (v 10)).left_comm]
  rw [(c_6_10 m (v 6) (v 10)).left_comm]
  rw [(c_15_10 m (v 15) (v 10)).left_comm]
  rw [(c_14_10 m (v 14) (v 10)).left_comm]
  rw [(c_13_10 m (v 13) (v 10)).left_comm]
  rw [(c_12_10 m (v 12) (v 10)).left_comm]
  rw [(c_3_10 m (v 3) (v 10)).left_comm]
  rw [(c_2_10 m (v 2) (v 10)).left_comm]
  rw [(c_11_10 m (v 11) (v 10)).left_comm]
  rw [add_suffix m 10 (v 10) (v 10),
    show (v 10) + (v 10) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_11 m ((v 9) + ((v 12) * (v 4))) (v 11)).left_comm]
  rw [(c_8_11 m ((v 8) + ((v 13) * (v 5))) (v 11)).left_comm]
  rw [(c_7_11 m (v 7) (v 11)).left_comm]

private theorem chunk_3 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 11 (v 11) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))) =
      X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))) := by
  rw [(c_6_11 m (v 6) (v 11)).left_comm]
  rw [(c_15_11 m (v 15) (v 11)).left_comm]
  rw [(c_14_11 m (v 14) (v 11)).left_comm]
  rw [(c_13_11 m (v 13) (v 11)).left_comm]
  rw [(c_12_11 m (v 12) (v 11)).left_comm]
  rw [(c_3_11 m (v 3) (v 11)).left_comm]
  rw [(c_2_11 m (v 2) (v 11)).left_comm]
  rw [add_suffix m 11 (v 11) (v 11),
    show (v 11) + (v 11) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_2 m ((v 9) + ((v 12) * (v 4))) (v 2)).left_comm]
  rw [(c_8_2 m ((v 8) + ((v 13) * (v 5))) (v 2)).left_comm]
  rw [(c_7_2 m (v 7) (v 2)).left_comm]
  rw [(c_6_2 m (v 6) (v 2)).left_comm]
  rw [(c_15_2 m (v 15) (v 2)).left_comm]
  rw [(c_14_2 m (v 14) (v 2)).left_comm]
  rw [(c_13_2 m (v 13) (v 2)).left_comm]
  rw [(c_12_2 m (v 12) (v 2)).left_comm]
  rw [(c_3_2 m (v 3) (v 2)).left_comm]
  rw [add_suffix m 2 (v 2) (v 2),
    show (v 2) + (v 2) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]

private theorem chunk_4 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))) =
      X m 13 (v 13) * (X m 14 ((v 12) * (v 13)) * (X m 14 (v 14) * (X m 15 ((v 12) * ((v 13) ^ 2)) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 10 ((v 12) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))) := by
  rw [(c_9_3 m ((v 9) + ((v 12) * (v 4))) (v 3)).left_comm]
  rw [(c_8_3 m ((v 8) + ((v 13) * (v 5))) (v 3)).left_comm]
  rw [(c_7_3 m (v 7) (v 3)).left_comm]
  rw [(c_6_3 m (v 6) (v 3)).left_comm]
  rw [(c_15_3 m (v 15) (v 3)).left_comm]
  rw [(c_14_3 m (v 14) (v 3)).left_comm]
  rw [(c_13_3 m (v 13) (v 3)).left_comm]
  rw [(c_12_3 m (v 12) (v 3)).left_comm]
  rw [add_suffix m 3 (v 3) (v 3),
    show (v 3) + (v 3) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_12 m ((v 9) + ((v 12) * (v 4))) (v 12)).left_comm]
  rw [(c_8_12 m ((v 8) + ((v 13) * (v 5))) (v 12)).left_comm]
  rw [(c_7_12 m (v 7) (v 12)).left_comm]
  have h12 : X m 6 (v 6) * X m 12 (v 12) = X m 12 (v 12) * X m 6 (v 6) * X m 10 ((v 12) * (v 6)) := by
    have h := s_6_12 m (v 6) (v 12)
    rw [show (v 6) * (v 12) = ((v 12) * (v 6)) by ring] at h
    exact h
  rw [swap_suffix h12]
  rw [(c_15_12 m (v 15) (v 12)).left_comm]
  rw [(c_14_12 m (v 14) (v 12)).left_comm]
  have h15 : X m 13 (v 13) * X m 12 (v 12) = X m 12 (v 12) * X m 13 (v 13) * X m 14 ((v 12) * (v 13)) * X m 15 ((v 12) * ((v 13) ^ 2)) := by
    have h := s_13_12 m (v 13) (v 12)
    rw [show (v 13) * (v 12) = ((v 12) * (v 13)) by ring, show (v 12) * (v 13) ^ 2 = ((v 12) * ((v 13) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h15]
  rw [add_suffix m 12 (v 12) (v 12),
    show (v 12) + (v 12) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_15_14 m ((v 12) * ((v 13) ^ 2)) (v 14)).left_comm]

private theorem chunk_5 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 13 (v 13) * (X m 14 ((v 12) * (v 13)) * (X m 14 (v 14) * (X m 15 ((v 12) * ((v 13) ^ 2)) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 10 ((v 12) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))) =
      X m 10 ((v 12) * (v 6)) * (X m 11 ((v 13) * (v 7)) * (X m 14 ((v 14) + ((v 12) * (v 13))) * (X m 15 ((v 15) + ((v 12) * ((v 13) ^ 2))) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5))) * (X m 14 (v 14) * (X m 9 ((v 9) + ((v 12) * (v 4))) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))) := by
  rw [add_suffix m 14 ((v 12) * (v 13)) (v 14),
    show ((v 12) * (v 13)) + (v 14) = ((v 14) + ((v 12) * (v 13))) by ring]
  rw [add_suffix m 15 ((v 12) * ((v 13) ^ 2)) (v 15),
    show ((v 12) * ((v 13) ^ 2)) + (v 15) = ((v 15) + ((v 12) * ((v 13) ^ 2))) by ring]
  rw [(c_6_10 m (v 6) ((v 12) * (v 6))).left_comm]
  rw [(c_15_10 m ((v 15) + ((v 12) * ((v 13) ^ 2))) ((v 12) * (v 6))).left_comm]
  rw [(c_14_10 m ((v 14) + ((v 12) * (v 13))) ((v 12) * (v 6))).left_comm]
  rw [(c_13_10 m (v 13) ((v 12) * (v 6))).left_comm]
  rw [(c_9_13 m ((v 9) + ((v 12) * (v 4))) (v 13)).left_comm]
  rw [(c_8_13 m ((v 8) + ((v 13) * (v 5))) (v 13)).left_comm]
  have h8 : X m 7 (v 7) * X m 13 (v 13) = X m 13 (v 13) * X m 7 (v 7) * X m 11 ((v 13) * (v 7)) := by
    have h := s_7_13 m (v 7) (v 13)
    rw [show (v 7) * (v 13) = ((v 13) * (v 7)) by ring] at h
    exact h
  rw [swap_suffix h8]
  rw [(c_6_13 m (v 6) (v 13)).left_comm]
  rw [(c_15_13 m ((v 15) + ((v 12) * ((v 13) ^ 2))) (v 13)).left_comm]
  rw [(c_14_13 m ((v 14) + ((v 12) * (v 13))) (v 13)).left_comm]
  rw [add_suffix m 13 (v 13) (v 13),
    show (v 13) + (v 13) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_7_11 m (v 7) ((v 13) * (v 7))).left_comm]
  rw [(c_6_11 m (v 6) ((v 13) * (v 7))).left_comm]
  rw [(c_15_11 m ((v 15) + ((v 12) * ((v 13) ^ 2))) ((v 13) * (v 7))).left_comm]
  rw [(c_14_11 m ((v 14) + ((v 12) * (v 13))) ((v 13) * (v 7))).left_comm]
  rw [(c_9_14 m ((v 9) + ((v 12) * (v 4))) (v 14)).left_comm]

private theorem chunk_6 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 ((v 12) * (v 6)) * (X m 11 ((v 13) * (v 7)) * (X m 14 ((v 14) + ((v 12) * (v 13))) * (X m 15 ((v 15) + ((v 12) * ((v 13) ^ 2))) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5))) * (X m 14 (v 14) * (X m 9 ((v 9) + ((v 12) * (v 4))) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))) =
      X m 10 ((v 12) * (v 6)) * (X m 11 ((v 13) * (v 7)) * (X m 14 ((v 12) * (v 13)) * (X m 15 ((v 12) * ((v 13) ^ 2)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 6) * (v 7))) * (X m 7 (v 7) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 6) * ((v 7) ^ 2))) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))) := by
  rw [(c_8_14 m ((v 8) + ((v 13) * (v 5))) (v 14)).left_comm]
  rw [(c_7_14 m (v 7) (v 14)).left_comm]
  rw [(c_6_14 m (v 6) (v 14)).left_comm]
  rw [(c_15_14 m ((v 15) + ((v 12) * ((v 13) ^ 2))) (v 14)).left_comm]
  rw [add_suffix m 14 ((v 14) + ((v 12) * (v 13))) (v 14),
    show ((v 14) + ((v 12) * (v 13))) + (v 14) = ((v 12) * (v 13)) by ring_nf; simp [CharTwo.two_eq_zero]]
  rw [(c_9_15 m ((v 9) + ((v 12) * (v 4))) (v 15)).left_comm]
  rw [(c_8_15 m ((v 8) + ((v 13) * (v 5))) (v 15)).left_comm]
  rw [(c_7_15 m (v 7) (v 15)).left_comm]
  rw [(c_6_15 m (v 6) (v 15)).left_comm]
  rw [add_suffix m 15 ((v 15) + ((v 12) * ((v 13) ^ 2))) (v 15),
    show ((v 15) + ((v 12) * ((v 13) ^ 2))) + (v 15) = ((v 12) * ((v 13) ^ 2)) by ring_nf; simp [CharTwo.two_eq_zero]]
  rw [(c_9_6 m ((v 9) + ((v 12) * (v 4))) (v 6)).left_comm]
  rw [(c_8_6 m ((v 8) + ((v 13) * (v 5))) (v 6)).left_comm]
  have h12 : X m 7 (v 7) * X m 6 (v 6) = X m 6 (v 6) * X m 7 (v 7) * X m 8 ((v 6) * (v 7)) * X m 9 ((v 6) * ((v 7) ^ 2)) := by
    have h := s_7_6 m (v 7) (v 6)
    rw [show (v 7) * (v 6) = ((v 6) * (v 7)) by ring, show (v 6) * (v 7) ^ 2 = ((v 6) * ((v 7) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h12]
  rw [add_suffix m 6 (v 6) (v 6),
    show (v 6) + (v 6) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_8 m ((v 6) * ((v 7) ^ 2)) ((v 8) + ((v 13) * (v 5)))).left_comm]
  rw [add_suffix m 8 ((v 6) * (v 7)) ((v 8) + ((v 13) * (v 5))),
    show ((v 6) * (v 7)) + ((v 8) + ((v 13) * (v 5))) = ((v 8) + ((v 13) * (v 5)) + ((v 6) * (v 7))) by ring]
  rw [add_suffix m 9 ((v 6) * ((v 7) ^ 2)) ((v 9) + ((v 12) * (v 4))),
    show ((v 6) * ((v 7) ^ 2)) + ((v 9) + ((v 12) * (v 4))) = ((v 9) + ((v 12) * (v 4)) + ((v 6) * ((v 7) ^ 2))) by ring]
  rw [(c_9_7 m ((v 9) + ((v 12) * (v 4)) + ((v 6) * ((v 7) ^ 2))) (v 7)).left_comm]

private theorem chunk_7 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 ((v 12) * (v 6)) * (X m 11 ((v 13) * (v 7)) * (X m 14 ((v 12) * (v 13)) * (X m 15 ((v 12) * ((v 13) ^ 2)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 6) * (v 7))) * (X m 7 (v 7) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 6) * ((v 7) ^ 2))) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))) =
      X m 10 ((v 12) * (v 6)) * (X m 11 ((v 13) * (v 7)) * (X m 14 ((v 12) * (v 13)) * (X m 15 ((v 12) * ((v 13) ^ 2)) * (X m 8 (((v 13) * (v 5)) + ((v 6) * (v 7))) * (X m 9 (((v 12) * (v 4)) + ((v 6) * ((v 7) ^ 2))) * (1)))))) := by
  rw [(c_8_7 m ((v 8) + ((v 13) * (v 5)) + ((v 6) * (v 7))) (v 7)).left_comm]
  rw [add_suffix m 7 (v 7) (v 7),
    show (v 7) + (v 7) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_8 m ((v 9) + ((v 12) * (v 4)) + ((v 6) * ((v 7) ^ 2))) (v 8)).left_comm]
  rw [add_suffix m 8 ((v 8) + ((v 13) * (v 5)) + ((v 6) * (v 7))) (v 8),
    show ((v 8) + ((v 13) * (v 5)) + ((v 6) * (v 7))) + (v 8) = (((v 13) * (v 5)) + ((v 6) * (v 7))) by ring_nf; simp [CharTwo.two_eq_zero]]
  rw [add_suffix m 9 ((v 9) + ((v 12) * (v 4)) + ((v 6) * ((v 7) ^ 2))) (v 9),
    show ((v 9) + ((v 12) * (v 4)) + ((v 6) * ((v 7) ^ 2))) + (v 9) = (((v 12) * (v 4)) + ((v 6) * ((v 7) ^ 2))) by ring_nf; simp [CharTwo.two_eq_zero]]

private theorem collected (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))) =
      splitWord m ![0, 0, 0, 0, 0, 0, 0, 0, (((v 13) * (v 5)) + ((v 6) * (v 7))), (((v 12) * (v 4)) + ((v 6) * ((v 7) ^ 2))), ((v 12) * (v 6)), ((v 13) * (v 7)), 0, 0, ((v 12) * (v 13)), ((v 12) * ((v 13) ^ 2)), 0, 0, 0, 0, 0, 0, 0, 0] := by
  have h := (chunk_0 m v).trans ((chunk_1 m v).trans ((chunk_2 m v).trans ((chunk_3 m v).trans ((chunk_4 m v).trans ((chunk_5 m v).trans ((chunk_6 m v).trans ((chunk_7 m v))))))))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk, xz, one_mul] using h

/-- Square-one detection on the indicated split-root section. -/
theorem equations (m : ℕ) (v : Fin 24 → CoefficientField m)
    (h0 : v 0 = 0)
    (h1 : v 1 = 0)
    (h16 : v 16 = 0)
    (h17 : v 17 = 0)
    (h18 : v 18 = 0)
    (h19 : v 19 = 0)
    (h20 : v 20 = 0)
    (h21 : v 21 = 0)
    (h22 : v 22 = 0)
    (h23 : v 23 = 0)
    (hsq : splitWord m v ^ 2 = 1) :
    ((v 12) * (v 13)) = 0 ∧ (((v 13) * (v 5)) + ((v 6) * (v 7))) = 0 := by
  have hh : X m 4 (v 4) * (X m 5 (v 5) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))) = 1 := by
    simpa only [splitWord, pow_two, h0, h1, h16, h17, h18, h19, h20, h21, h22, h23, xz, one_mul, mul_assoc] using hsq
  have hz : splitWord m (fun _ => 0) = 1 := by simp only [splitWord, xz, mul_one]
  have hv := splitWord_injective m ((collected m v).symm.trans (hh.trans hz.symm))
  constructor
  · exact congrFun hv 14
  · exact congrFun hv 8

end ReeF4.ElementaryTwoBound.RootCalculations.LeftSquareCollection
