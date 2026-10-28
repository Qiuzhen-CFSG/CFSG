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
namespace ReeF4.ElementaryTwoBound.RootCalculations.RightSquareCollection
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent.OuterElimination
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local irreducible] X
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

private theorem c_9_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 20 b) :=
  xc m 9 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 21 b) :=
  xc m 9 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_10_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 16 b) :=
  xc m 10 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_10_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 17 b) :=
  xc m 10 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 10 b) :=
  xc m 11 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 16 b) :=
  xc m 11 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 17 b) :=
  xc m 11 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 10 b) :=
  xc m 12 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 11 b) :=
  xc m 12 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 16 b) :=
  xc m 12 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 17 b) :=
  xc m 12 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 10 b) :=
  xc m 13 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 11 b) :=
  xc m 13 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_13_12 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 12 b = X m 12 b * X m 13 a * X m 14 (a*b) * X m 15 (b*a^2) := by
  simpa only [mul_comm] using xb m 12 13 14 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_13_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 16 b) :=
  xc m 13 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 17 b) :=
  xc m 13 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_17_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 16 b) :=
  xc m 17 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_21_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 10 b) :=
  xc m 21 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 11 b) :=
  xc m 21 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 12 b) :=
  xc m 21 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 13 b) :=
  xc m 21 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 14 b) :=
  xc m 21 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 15 b) :=
  xc m 21 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 16 b) :=
  xc m 21 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 17 b) :=
  xc m 21 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 20 b) :=
  xc m 21 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem chunk_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))) =
      X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 16) * (v 6))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) := by
  rw [(c_9_16 m (v 9) (v 16)).left_comm]
  rw [(c_8_16 m (v 8) (v 16)).left_comm]
  rw [(c_7_16 m (v 7) (v 16)).left_comm]
  have h3 : X m 6 (v 6) * X m 16 (v 16) = X m 16 (v 16) * X m 6 (v 6) * X m 15 ((v 16) * (v 6)) := by
    have h := s_6_16 m (v 6) (v 16)
    rw [show (v 6) * (v 16) = ((v 16) * (v 6)) by ring] at h
    exact h
  rw [swap_suffix h3]
  rw [(c_21_16 m (v 21) (v 16)).left_comm]
  rw [(c_20_16 m (v 20) (v 16)).left_comm]
  rw [(c_15_16 m (v 15) (v 16)).left_comm]
  rw [(c_14_16 m (v 14) (v 16)).left_comm]
  rw [(c_13_16 m (v 13) (v 16)).left_comm]
  rw [(c_12_16 m (v 12) (v 16)).left_comm]
  rw [(c_11_16 m (v 11) (v 16)).left_comm]
  rw [(c_10_16 m (v 10) (v 16)).left_comm]
  rw [(c_17_16 m (v 17) (v 16)).left_comm]
  rw [add_suffix m 16 (v 16) (v 16),
    show (v 16) + (v 16) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_6_15 m (v 6) ((v 16) * (v 6))).left_comm]
  rw [(c_21_15 m (v 21) ((v 16) * (v 6))).left_comm]
  rw [(c_20_15 m (v 20) ((v 16) * (v 6))).left_comm]
  rw [add_suffix m 15 (v 15) ((v 16) * (v 6)),
    show (v 15) + ((v 16) * (v 6)) = ((v 15) + ((v 16) * (v 6))) by ring]

private theorem chunk_1 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 16) * (v 6))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) =
      X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 14 ((v 17) * (v 7)) * (X m 15 ((v 15) + ((v 16) * (v 6))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))) := by
  rw [(c_9_17 m (v 9) (v 17)).left_comm]
  rw [(c_8_17 m (v 8) (v 17)).left_comm]
  have h2 : X m 7 (v 7) * X m 17 (v 17) = X m 17 (v 17) * X m 7 (v 7) * X m 14 ((v 17) * (v 7)) := by
    have h := s_7_17 m (v 7) (v 17)
    rw [show (v 7) * (v 17) = ((v 17) * (v 7)) by ring] at h
    exact h
  rw [swap_suffix h2]
  rw [(c_6_17 m (v 6) (v 17)).left_comm]
  rw [(c_21_17 m (v 21) (v 17)).left_comm]
  rw [(c_20_17 m (v 20) (v 17)).left_comm]
  rw [(c_15_17 m ((v 15) + ((v 16) * (v 6))) (v 17)).left_comm]
  rw [(c_14_17 m (v 14) (v 17)).left_comm]
  rw [(c_13_17 m (v 13) (v 17)).left_comm]
  rw [(c_12_17 m (v 12) (v 17)).left_comm]
  rw [(c_11_17 m (v 11) (v 17)).left_comm]
  rw [(c_10_17 m (v 10) (v 17)).left_comm]
  rw [add_suffix m 17 (v 17) (v 17),
    show (v 17) + (v 17) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_7_14 m (v 7) ((v 17) * (v 7))).left_comm]
  rw [(c_6_14 m (v 6) ((v 17) * (v 7))).left_comm]
  rw [(c_21_14 m (v 21) ((v 17) * (v 7))).left_comm]
  rw [(c_20_14 m (v 20) ((v 17) * (v 7))).left_comm]
  rw [(c_15_14 m ((v 15) + ((v 16) * (v 6))) ((v 17) * (v 7))).left_comm]

private theorem chunk_2 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 14 ((v 17) * (v 7)) * (X m 15 ((v 15) + ((v 16) * (v 6))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))) =
      X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 17) * (v 7))) * (X m 15 ((v 15) + ((v 16) * (v 6))) * (X m 20 (v 20) * (X m 11 (v 11) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))) := by
  rw [add_suffix m 14 (v 14) ((v 17) * (v 7)),
    show (v 14) + ((v 17) * (v 7)) = ((v 14) + ((v 17) * (v 7))) by ring]
  rw [(c_9_10 m (v 9) (v 10)).left_comm]
  rw [(c_8_10 m (v 8) (v 10)).left_comm]
  rw [(c_7_10 m (v 7) (v 10)).left_comm]
  rw [(c_6_10 m (v 6) (v 10)).left_comm]
  rw [(c_21_10 m (v 21) (v 10)).left_comm]
  rw [(c_20_10 m (v 20) (v 10)).left_comm]
  rw [(c_15_10 m ((v 15) + ((v 16) * (v 6))) (v 10)).left_comm]
  rw [(c_14_10 m ((v 14) + ((v 17) * (v 7))) (v 10)).left_comm]
  rw [(c_13_10 m (v 13) (v 10)).left_comm]
  rw [(c_12_10 m (v 12) (v 10)).left_comm]
  rw [(c_11_10 m (v 11) (v 10)).left_comm]
  rw [add_suffix m 10 (v 10) (v 10),
    show (v 10) + (v 10) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_11 m (v 9) (v 11)).left_comm]
  rw [(c_8_11 m (v 8) (v 11)).left_comm]
  rw [(c_7_11 m (v 7) (v 11)).left_comm]
  rw [(c_6_11 m (v 6) (v 11)).left_comm]
  rw [(c_21_11 m (v 21) (v 11)).left_comm]

private theorem chunk_3 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 17) * (v 7))) * (X m 15 ((v 15) + ((v 16) * (v 6))) * (X m 20 (v 20) * (X m 11 (v 11) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))) =
      X m 13 (v 13) * (X m 14 ((v 14) + ((v 12) * (v 13)) + ((v 17) * (v 7))) * (X m 15 ((v 12) * ((v 13) ^ 2)) * (X m 15 ((v 15) + ((v 16) * (v 6))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 10 ((v 12) * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))) := by
  rw [(c_20_11 m (v 20) (v 11)).left_comm]
  rw [(c_15_11 m ((v 15) + ((v 16) * (v 6))) (v 11)).left_comm]
  rw [(c_14_11 m ((v 14) + ((v 17) * (v 7))) (v 11)).left_comm]
  rw [(c_13_11 m (v 13) (v 11)).left_comm]
  rw [(c_12_11 m (v 12) (v 11)).left_comm]
  rw [add_suffix m 11 (v 11) (v 11),
    show (v 11) + (v 11) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_12 m (v 9) (v 12)).left_comm]
  rw [(c_8_12 m (v 8) (v 12)).left_comm]
  rw [(c_7_12 m (v 7) (v 12)).left_comm]
  have h9 : X m 6 (v 6) * X m 12 (v 12) = X m 12 (v 12) * X m 6 (v 6) * X m 10 ((v 12) * (v 6)) := by
    have h := s_6_12 m (v 6) (v 12)
    rw [show (v 6) * (v 12) = ((v 12) * (v 6)) by ring] at h
    exact h
  rw [swap_suffix h9]
  rw [(c_21_12 m (v 21) (v 12)).left_comm]
  rw [(c_20_12 m (v 20) (v 12)).left_comm]
  rw [(c_15_12 m ((v 15) + ((v 16) * (v 6))) (v 12)).left_comm]
  rw [(c_14_12 m ((v 14) + ((v 17) * (v 7))) (v 12)).left_comm]
  have h14 : X m 13 (v 13) * X m 12 (v 12) = X m 12 (v 12) * X m 13 (v 13) * X m 14 ((v 12) * (v 13)) * X m 15 ((v 12) * ((v 13) ^ 2)) := by
    have h := s_13_12 m (v 13) (v 12)
    rw [show (v 13) * (v 12) = ((v 12) * (v 13)) by ring, show (v 12) * (v 13) ^ 2 = ((v 12) * ((v 13) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h14]
  rw [add_suffix m 12 (v 12) (v 12),
    show (v 12) + (v 12) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_15_14 m ((v 12) * ((v 13) ^ 2)) ((v 14) + ((v 17) * (v 7)))).left_comm]
  rw [add_suffix m 14 ((v 12) * (v 13)) ((v 14) + ((v 17) * (v 7))),
    show ((v 12) * (v 13)) + ((v 14) + ((v 17) * (v 7))) = ((v 14) + ((v 12) * (v 13)) + ((v 17) * (v 7))) by ring]

private theorem chunk_4 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 13 (v 13) * (X m 14 ((v 14) + ((v 12) * (v 13)) + ((v 17) * (v 7))) * (X m 15 ((v 12) * ((v 13) ^ 2)) * (X m 15 ((v 15) + ((v 16) * (v 6))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 10 ((v 12) * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))) =
      X m 10 ((v 12) * (v 6)) * (X m 14 ((v 14) + ((v 12) * (v 13)) + ((v 17) * (v 7))) * (X m 15 ((v 15) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 11 ((v 13) * (v 7)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))) := by
  rw [add_suffix m 15 ((v 12) * ((v 13) ^ 2)) ((v 15) + ((v 16) * (v 6))),
    show ((v 12) * ((v 13) ^ 2)) + ((v 15) + ((v 16) * (v 6))) = ((v 15) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) by ring]
  rw [(c_6_10 m (v 6) ((v 12) * (v 6))).left_comm]
  rw [(c_21_10 m (v 21) ((v 12) * (v 6))).left_comm]
  rw [(c_20_10 m (v 20) ((v 12) * (v 6))).left_comm]
  rw [(c_15_10 m ((v 15) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) ((v 12) * (v 6))).left_comm]
  rw [(c_14_10 m ((v 14) + ((v 12) * (v 13)) + ((v 17) * (v 7))) ((v 12) * (v 6))).left_comm]
  rw [(c_13_10 m (v 13) ((v 12) * (v 6))).left_comm]
  rw [(c_9_13 m (v 9) (v 13)).left_comm]
  rw [(c_8_13 m (v 8) (v 13)).left_comm]
  have h9 : X m 7 (v 7) * X m 13 (v 13) = X m 13 (v 13) * X m 7 (v 7) * X m 11 ((v 13) * (v 7)) := by
    have h := s_7_13 m (v 7) (v 13)
    rw [show (v 7) * (v 13) = ((v 13) * (v 7)) by ring] at h
    exact h
  rw [swap_suffix h9]
  rw [(c_6_13 m (v 6) (v 13)).left_comm]
  rw [(c_21_13 m (v 21) (v 13)).left_comm]
  rw [(c_20_13 m (v 20) (v 13)).left_comm]
  rw [(c_15_13 m ((v 15) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) (v 13)).left_comm]
  rw [(c_14_13 m ((v 14) + ((v 12) * (v 13)) + ((v 17) * (v 7))) (v 13)).left_comm]
  rw [add_suffix m 13 (v 13) (v 13),
    show (v 13) + (v 13) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_7_11 m (v 7) ((v 13) * (v 7))).left_comm]
  rw [(c_6_11 m (v 6) ((v 13) * (v 7))).left_comm]

private theorem chunk_5 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 ((v 12) * (v 6)) * (X m 14 ((v 14) + ((v 12) * (v 13)) + ((v 17) * (v 7))) * (X m 15 ((v 15) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 11 ((v 13) * (v 7)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))) =
      X m 10 ((v 12) * (v 6)) * (X m 11 ((v 13) * (v 7)) * (X m 14 (((v 12) * (v 13)) + ((v 17) * (v 7))) * (X m 15 ((v 15) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))) := by
  rw [(c_21_11 m (v 21) ((v 13) * (v 7))).left_comm]
  rw [(c_20_11 m (v 20) ((v 13) * (v 7))).left_comm]
  rw [(c_15_11 m ((v 15) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) ((v 13) * (v 7))).left_comm]
  rw [(c_14_11 m ((v 14) + ((v 12) * (v 13)) + ((v 17) * (v 7))) ((v 13) * (v 7))).left_comm]
  rw [(c_9_14 m (v 9) (v 14)).left_comm]
  rw [(c_8_14 m (v 8) (v 14)).left_comm]
  rw [(c_7_14 m (v 7) (v 14)).left_comm]
  rw [(c_6_14 m (v 6) (v 14)).left_comm]
  rw [(c_21_14 m (v 21) (v 14)).left_comm]
  rw [(c_20_14 m (v 20) (v 14)).left_comm]
  rw [(c_15_14 m ((v 15) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) (v 14)).left_comm]
  rw [add_suffix m 14 ((v 14) + ((v 12) * (v 13)) + ((v 17) * (v 7))) (v 14),
    show ((v 14) + ((v 12) * (v 13)) + ((v 17) * (v 7))) + (v 14) = (((v 12) * (v 13)) + ((v 17) * (v 7))) by ring_nf; simp [CharTwo.two_eq_zero]]
  rw [(c_9_15 m (v 9) (v 15)).left_comm]
  rw [(c_8_15 m (v 8) (v 15)).left_comm]
  rw [(c_7_15 m (v 7) (v 15)).left_comm]
  rw [(c_6_15 m (v 6) (v 15)).left_comm]
  rw [(c_21_15 m (v 21) (v 15)).left_comm]
  rw [(c_20_15 m (v 20) (v 15)).left_comm]

private theorem chunk_6 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 ((v 12) * (v 6)) * (X m 11 ((v 13) * (v 7)) * (X m 14 (((v 12) * (v 13)) + ((v 17) * (v 7))) * (X m 15 ((v 15) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))) =
      X m 10 ((v 12) * (v 6)) * (X m 11 ((v 13) * (v 7)) * (X m 14 (((v 12) * (v 13)) + ((v 17) * (v 7))) * (X m 15 (((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 6) * (v 7))) * (X m 9 ((v 6) * ((v 7) ^ 2)) * (X m 9 (v 9) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))) := by
  rw [add_suffix m 15 ((v 15) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) (v 15),
    show ((v 15) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) + (v 15) = (((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) by ring_nf; simp [CharTwo.two_eq_zero]]
  rw [(c_9_20 m (v 9) (v 20)).left_comm]
  rw [(c_8_20 m (v 8) (v 20)).left_comm]
  rw [(c_7_20 m (v 7) (v 20)).left_comm]
  rw [(c_6_20 m (v 6) (v 20)).left_comm]
  rw [(c_21_20 m (v 21) (v 20)).left_comm]
  rw [add_suffix m 20 (v 20) (v 20),
    show (v 20) + (v 20) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_21 m (v 9) (v 21)).left_comm]
  rw [(c_8_21 m (v 8) (v 21)).left_comm]
  rw [(c_7_21 m (v 7) (v 21)).left_comm]
  rw [(c_6_21 m (v 6) (v 21)).left_comm]
  rw [add_suffix m 21 (v 21) (v 21),
    show (v 21) + (v 21) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_6 m (v 9) (v 6)).left_comm]
  rw [(c_8_6 m (v 8) (v 6)).left_comm]
  have h14 : X m 7 (v 7) * X m 6 (v 6) = X m 6 (v 6) * X m 7 (v 7) * X m 8 ((v 6) * (v 7)) * X m 9 ((v 6) * ((v 7) ^ 2)) := by
    have h := s_7_6 m (v 7) (v 6)
    rw [show (v 7) * (v 6) = ((v 6) * (v 7)) by ring, show (v 6) * (v 7) ^ 2 = ((v 6) * ((v 7) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h14]
  rw [add_suffix m 6 (v 6) (v 6),
    show (v 6) + (v 6) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_8 m ((v 6) * ((v 7) ^ 2)) (v 8)).left_comm]
  rw [add_suffix m 8 ((v 6) * (v 7)) (v 8),
    show ((v 6) * (v 7)) + (v 8) = ((v 8) + ((v 6) * (v 7))) by ring]

private theorem chunk_7 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 ((v 12) * (v 6)) * (X m 11 ((v 13) * (v 7)) * (X m 14 (((v 12) * (v 13)) + ((v 17) * (v 7))) * (X m 15 (((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 6) * (v 7))) * (X m 9 ((v 6) * ((v 7) ^ 2)) * (X m 9 (v 9) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))) =
      X m 10 ((v 12) * (v 6)) * (X m 11 ((v 13) * (v 7)) * (X m 14 (((v 12) * (v 13)) + ((v 17) * (v 7))) * (X m 15 (((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))) * (X m 8 ((v 6) * (v 7)) * (X m 9 ((v 6) * ((v 7) ^ 2)) * (1)))))) := by
  rw [add_suffix m 9 ((v 6) * ((v 7) ^ 2)) (v 9),
    show ((v 6) * ((v 7) ^ 2)) + (v 9) = ((v 9) + ((v 6) * ((v 7) ^ 2))) by ring]
  rw [(c_9_7 m ((v 9) + ((v 6) * ((v 7) ^ 2))) (v 7)).left_comm]
  rw [(c_8_7 m ((v 8) + ((v 6) * (v 7))) (v 7)).left_comm]
  rw [add_suffix m 7 (v 7) (v 7),
    show (v 7) + (v 7) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_8 m ((v 9) + ((v 6) * ((v 7) ^ 2))) (v 8)).left_comm]
  rw [add_suffix m 8 ((v 8) + ((v 6) * (v 7))) (v 8),
    show ((v 8) + ((v 6) * (v 7))) + (v 8) = ((v 6) * (v 7)) by ring_nf; simp [CharTwo.two_eq_zero]]
  rw [add_suffix m 9 ((v 9) + ((v 6) * ((v 7) ^ 2))) (v 9),
    show ((v 9) + ((v 6) * ((v 7) ^ 2))) + (v 9) = ((v 6) * ((v 7) ^ 2)) by ring_nf; simp [CharTwo.two_eq_zero]]

private theorem collected (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))) =
      splitWord m ![0, 0, 0, 0, 0, 0, 0, 0, ((v 6) * (v 7)), ((v 6) * ((v 7) ^ 2)), ((v 12) * (v 6)), ((v 13) * (v 7)), 0, 0, (((v 12) * (v 13)) + ((v 17) * (v 7))), (((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6))), 0, 0, 0, 0, 0, 0, 0, 0] := by
  have h := (chunk_0 m v).trans ((chunk_1 m v).trans ((chunk_2 m v).trans ((chunk_3 m v).trans ((chunk_4 m v).trans ((chunk_5 m v).trans ((chunk_6 m v).trans ((chunk_7 m v))))))))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk, xz, one_mul] using h

/-- Square-one detection on the indicated split-root section. -/
theorem equations (m : ℕ) (v : Fin 24 → CoefficientField m)
    (h0 : v 0 = 0)
    (h1 : v 1 = 0)
    (h2 : v 2 = 0)
    (h3 : v 3 = 0)
    (h4 : v 4 = 0)
    (h5 : v 5 = 0)
    (h18 : v 18 = 0)
    (h19 : v 19 = 0)
    (h22 : v 22 = 0)
    (h23 : v 23 = 0)
    (hsq : splitWord m v ^ 2 = 1) :
    ((v 6) * (v 7)) = 0 ∧ (((v 12) * (v 13)) + ((v 17) * (v 7))) = 0 := by
  have hh : X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))) = 1 := by
    simpa only [splitWord, pow_two, h0, h1, h2, h3, h4, h5, h18, h19, h22, h23, xz, one_mul, mul_assoc] using hsq
  have hz : splitWord m (fun _ => 0) = 1 := by simp only [splitWord, xz, mul_one]
  have hv := splitWord_injective m ((collected m v).symm.trans (hh.trans hz.symm))
  constructor
  · exact congrFun hv 8
  · exact congrFun hv 14

end ReeF4.ElementaryTwoBound.RootCalculations.RightSquareCollection
