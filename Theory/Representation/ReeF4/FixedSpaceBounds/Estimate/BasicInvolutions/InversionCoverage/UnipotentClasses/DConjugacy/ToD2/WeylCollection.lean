module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords
/-!
# Checked split-root collection for transport from D to D₂

Each adjacent exchange uses the proved F₄ matrix relations. Unique positive
split coordinates give the scalar consequences used by the fixed-group
transport in `ToD2`. The Python generator is only a proof-writing tool.
Source: GLS3 Table 2.4, 2.4.5(d), and the sections of Lemma 3.3.9.
-/
public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2.WeylCollection
open ReeF4.Parabolics ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
open ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local irreducible] X
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

private theorem c_6_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 2 b) :=
  xc m 6 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 3 b) :=
  xc m 6 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_8_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 6 b) :=
  xc m 8 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_7 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 7 b) :=
  xc m 8 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 10 b) :=
  xc m 8 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_11_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 10 b) :=
  xc m 11 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 10 b) :=
  xc m 12 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 11 b) :=
  xc m 12 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 11 b) :=
  xc m 13 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 3 b) :=
  xc m 14 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem s_21_2 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 2 b = X m 2 b * X m 21 a * X m 14 (a*b) * X m 9 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 21 2 14 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 14 (a*b)) (xx m 9 (a*b^2))
    (xc m 14 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem s_21_3 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 3 b = X m 3 b * X m 21 a * X m 10 (a*b) :=
  xs m 21 3 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

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

private theorem chunk_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 4) * (X m 17 (v 5) * (X m 4 (v 16) * (X m 5 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 (v 14) * (X m 9 (v 15) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 (v 8) * (X m 15 (v 9) * (1)))))))))))))))))) =
      X m 4 (v 16) * (X m 5 (v 17) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 (v 10) * (X m 11 ((v 11) + ((v 2) * (v 20))) * (X m 2 (v 20) * (X m 14 ((v 20) * (v 3)) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 (v 14) * (X m 9 ((v 3) * ((v 20) ^ 2)) * (X m 9 (v 15) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 (v 8) * (X m 15 (v 9) * (1)))))))))))))))))))) := by
  rw [(c_17_4 m (v 5) (v 16)).left_comm]
  rw [(c_16_4 m (v 4) (v 16)).left_comm]
  rw [(c_17_5 m (v 5) (v 17)).left_comm]
  rw [(c_16_5 m (v 4) (v 17)).left_comm]
  rw [(c_9_2 m (v 15) (v 20)).left_comm]
  rw [(c_8_2 m (v 14) (v 20)).left_comm]
  rw [(c_7_2 m (v 13) (v 20)).left_comm]
  rw [(c_6_2 m (v 12) (v 20)).left_comm]
  have h8 : X m 21 (v 3) * X m 2 (v 20) = X m 2 (v 20) * X m 21 (v 3) * X m 14 ((v 20) * (v 3)) * X m 9 ((v 3) * ((v 20) ^ 2)) := by
    have h := s_21_2 m (v 3) (v 20)
    rw [show (v 3) * (v 20) = ((v 20) * (v 3)) by ring, show (v 3) * (v 20) ^ 2 = ((v 3) * ((v 20) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h8]
  have h9 : X m 20 (v 2) * X m 2 (v 20) = X m 2 (v 20) * X m 20 (v 2) * X m 11 ((v 2) * (v 20)) := by
    have h := s_20_2 m (v 2) (v 20)
    rw [show (v 2) * (v 20) = ((v 2) * (v 20)) by ring] at h
    exact h
  rw [swap_suffix h9]
  rw [(c_20_11 m (v 2) ((v 2) * (v 20))).left_comm]
  rw [(c_2_11 m (v 20) ((v 2) * (v 20))).left_comm]
  rw [add_suffix m 11 (v 11) ((v 2) * (v 20)),
    show (v 11) + ((v 2) * (v 20)) = ((v 11) + ((v 2) * (v 20))) by ring]
  rw [(c_21_14 m (v 3) ((v 20) * (v 3))).left_comm]
  rw [(c_20_14 m (v 2) ((v 20) * (v 3))).left_comm]
  rw [(c_9_6 m ((v 3) * ((v 20) ^ 2)) (v 12)).left_comm]
  rw [(c_9_7 m ((v 3) * ((v 20) ^ 2)) (v 13)).left_comm]
  rw [(c_9_8 m ((v 3) * ((v 20) ^ 2)) (v 14)).left_comm]

private theorem chunk_1 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 16) * (X m 5 (v 17) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 (v 10) * (X m 11 ((v 11) + ((v 2) * (v 20))) * (X m 2 (v 20) * (X m 14 ((v 20) * (v 3)) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 (v 14) * (X m 9 ((v 3) * ((v 20) ^ 2)) * (X m 9 (v 15) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 (v 8) * (X m 15 (v 9) * (1)))))))))))))))))))) =
      X m 4 (v 16) * (X m 5 (v 17) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 (v 10) * (X m 11 ((v 11) + ((v 2) * (v 20))) * (X m 10 ((v 21) * (v 3)) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 14 ((v 20) * (v 3)) * (X m 15 ((v 21) * ((v 2) ^ 2)) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 8 ((v 2) * (v 21)) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 (v 14) * (X m 9 ((v 15) + ((v 3) * ((v 20) ^ 2))) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 (v 8) * (X m 15 (v 9) * (1)))))))))))))))))))))) := by
  rw [add_suffix m 9 ((v 3) * ((v 20) ^ 2)) (v 15),
    show ((v 3) * ((v 20) ^ 2)) + (v 15) = ((v 15) + ((v 3) * ((v 20) ^ 2))) by ring]
  rw [(c_9_3 m ((v 15) + ((v 3) * ((v 20) ^ 2))) (v 21)).left_comm]
  rw [(c_8_3 m (v 14) (v 21)).left_comm]
  rw [(c_7_3 m (v 13) (v 21)).left_comm]
  rw [(c_6_3 m (v 12) (v 21)).left_comm]
  have h5 : X m 21 (v 3) * X m 3 (v 21) = X m 3 (v 21) * X m 21 (v 3) * X m 10 ((v 21) * (v 3)) := by
    have h := s_21_3 m (v 3) (v 21)
    rw [show (v 3) * (v 21) = ((v 21) * (v 3)) by ring] at h
    exact h
  rw [swap_suffix h5]
  have h6 : X m 20 (v 2) * X m 3 (v 21) = X m 3 (v 21) * X m 20 (v 2) * X m 8 ((v 2) * (v 21)) * X m 15 ((v 21) * ((v 2) ^ 2)) := by
    have h := s_20_3 m (v 2) (v 21)
    rw [show (v 2) * (v 21) = ((v 2) * (v 21)) by ring, show (v 21) * (v 2) ^ 2 = ((v 21) * ((v 2) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h6]
  rw [(c_14_3 m ((v 20) * (v 3)) (v 21)).left_comm]
  rw [(c_8_15 m ((v 2) * (v 21)) ((v 21) * ((v 2) ^ 2))).left_comm]
  rw [(c_20_15 m (v 2) ((v 21) * ((v 2) ^ 2))).left_comm]
  rw [(c_8_21 m ((v 2) * (v 21)) (v 3)).left_comm]
  rw [(c_8_10 m ((v 2) * (v 21)) ((v 21) * (v 3))).left_comm]
  rw [(c_21_10 m (v 3) ((v 21) * (v 3))).left_comm]
  rw [(c_20_10 m (v 2) ((v 21) * (v 3))).left_comm]
  rw [(c_15_10 m ((v 21) * ((v 2) ^ 2)) ((v 21) * (v 3))).left_comm]
  rw [(c_14_10 m ((v 20) * (v 3)) ((v 21) * (v 3))).left_comm]
  rw [(c_3_10 m (v 21) ((v 21) * (v 3))).left_comm]
  rw [(c_2_10 m (v 20) ((v 21) * (v 3))).left_comm]

private theorem chunk_2 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 16) * (X m 5 (v 17) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 (v 10) * (X m 11 ((v 11) + ((v 2) * (v 20))) * (X m 10 ((v 21) * (v 3)) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 14 ((v 20) * (v 3)) * (X m 15 ((v 21) * ((v 2) ^ 2)) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 8 ((v 2) * (v 21)) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 (v 14) * (X m 9 ((v 15) + ((v 3) * ((v 20) ^ 2))) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 (v 8) * (X m 15 (v 9) * (1)))))))))))))))))))))) =
      X m 4 (v 16) * (X m 5 (v 17) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 ((v 10) + ((v 21) * (v 3))) * (X m 11 ((v 11) + ((v 2) * (v 20))) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 10 ((v 12) * (v 6)) * (X m 14 ((v 20) * (v 3)) * (X m 15 ((v 21) * ((v 2) ^ 2)) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 ((v 14) + ((v 2) * (v 21))) * (X m 9 ((v 15) + ((v 3) * ((v 20) ^ 2))) * (X m 13 (v 7) * (X m 14 (v 8) * (X m 15 (v 9) * (1))))))))))))))))))))) := by
  rw [(c_11_10 m ((v 11) + ((v 2) * (v 20))) ((v 21) * (v 3))).left_comm]
  rw [add_suffix m 10 (v 10) ((v 21) * (v 3)),
    show (v 10) + ((v 21) * (v 3)) = ((v 10) + ((v 21) * (v 3))) by ring]
  rw [(c_8_6 m ((v 2) * (v 21)) (v 12)).left_comm]
  rw [(c_8_7 m ((v 2) * (v 21)) (v 13)).left_comm]
  rw [add_suffix m 8 ((v 2) * (v 21)) (v 14),
    show ((v 2) * (v 21)) + (v 14) = ((v 14) + ((v 2) * (v 21))) by ring]
  rw [(c_9_12 m ((v 15) + ((v 3) * ((v 20) ^ 2))) (v 6)).left_comm]
  rw [(c_8_12 m ((v 14) + ((v 2) * (v 21))) (v 6)).left_comm]
  rw [(c_7_12 m (v 13) (v 6)).left_comm]
  have h8 : X m 6 (v 12) * X m 12 (v 6) = X m 12 (v 6) * X m 6 (v 12) * X m 10 ((v 12) * (v 6)) := by
    have h := s_6_12 m (v 12) (v 6)
    rw [show (v 12) * (v 6) = ((v 12) * (v 6)) by ring] at h
    exact h
  rw [swap_suffix h8]
  rw [(c_21_12 m (v 3) (v 6)).left_comm]
  rw [(c_20_12 m (v 2) (v 6)).left_comm]
  rw [(c_15_12 m ((v 21) * ((v 2) ^ 2)) (v 6)).left_comm]
  rw [(c_14_12 m ((v 20) * (v 3)) (v 6)).left_comm]
  rw [(c_6_10 m (v 12) ((v 12) * (v 6))).left_comm]
  rw [(c_21_10 m (v 3) ((v 12) * (v 6))).left_comm]
  rw [(c_20_10 m (v 2) ((v 12) * (v 6))).left_comm]
  rw [(c_15_10 m ((v 21) * ((v 2) ^ 2)) ((v 12) * (v 6))).left_comm]
  rw [(c_14_10 m ((v 20) * (v 3)) ((v 12) * (v 6))).left_comm]

private theorem chunk_3 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 16) * (X m 5 (v 17) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 ((v 10) + ((v 21) * (v 3))) * (X m 11 ((v 11) + ((v 2) * (v 20))) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 10 ((v 12) * (v 6)) * (X m 14 ((v 20) * (v 3)) * (X m 15 ((v 21) * ((v 2) ^ 2)) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 ((v 14) + ((v 2) * (v 21))) * (X m 9 ((v 15) + ((v 3) * ((v 20) ^ 2))) * (X m 13 (v 7) * (X m 14 (v 8) * (X m 15 (v 9) * (1))))))))))))))))))))) =
      X m 4 (v 16) * (X m 5 (v 17) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 ((v 10) + ((v 12) * (v 6)) + ((v 21) * (v 3))) * (X m 11 ((v 11) + ((v 2) * (v 20))) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 20) * (v 3)) * (X m 11 ((v 13) * (v 7)) * (X m 15 ((v 21) * ((v 2) ^ 2)) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 ((v 14) + ((v 2) * (v 21))) * (X m 9 ((v 15) + ((v 3) * ((v 20) ^ 2))) * (X m 14 (v 8) * (X m 15 (v 9) * (1))))))))))))))))))))) := by
  rw [(c_12_10 m (v 6) ((v 12) * (v 6))).left_comm]
  rw [(c_3_10 m (v 21) ((v 12) * (v 6))).left_comm]
  rw [(c_2_10 m (v 20) ((v 12) * (v 6))).left_comm]
  rw [(c_11_10 m ((v 11) + ((v 2) * (v 20))) ((v 12) * (v 6))).left_comm]
  rw [add_suffix m 10 ((v 10) + ((v 21) * (v 3))) ((v 12) * (v 6)),
    show ((v 10) + ((v 21) * (v 3))) + ((v 12) * (v 6)) = ((v 10) + ((v 12) * (v 6)) + ((v 21) * (v 3))) by ring]
  rw [(c_9_13 m ((v 15) + ((v 3) * ((v 20) ^ 2))) (v 7)).left_comm]
  rw [(c_8_13 m ((v 14) + ((v 2) * (v 21))) (v 7)).left_comm]
  have h7 : X m 7 (v 13) * X m 13 (v 7) = X m 13 (v 7) * X m 7 (v 13) * X m 11 ((v 13) * (v 7)) := by
    have h := s_7_13 m (v 13) (v 7)
    rw [show (v 13) * (v 7) = ((v 13) * (v 7)) by ring] at h
    exact h
  rw [swap_suffix h7]
  rw [(c_6_13 m (v 12) (v 7)).left_comm]
  rw [(c_21_13 m (v 3) (v 7)).left_comm]
  rw [(c_20_13 m (v 2) (v 7)).left_comm]
  rw [(c_15_13 m ((v 21) * ((v 2) ^ 2)) (v 7)).left_comm]
  rw [(c_14_13 m ((v 20) * (v 3)) (v 7)).left_comm]
  rw [(c_7_11 m (v 13) ((v 13) * (v 7))).left_comm]
  rw [(c_6_11 m (v 12) ((v 13) * (v 7))).left_comm]
  rw [(c_21_11 m (v 3) ((v 13) * (v 7))).left_comm]
  rw [(c_20_11 m (v 2) ((v 13) * (v 7))).left_comm]
  rw [(c_15_11 m ((v 21) * ((v 2) ^ 2)) ((v 13) * (v 7))).left_comm]

private theorem chunk_4 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 16) * (X m 5 (v 17) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 ((v 10) + ((v 12) * (v 6)) + ((v 21) * (v 3))) * (X m 11 ((v 11) + ((v 2) * (v 20))) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 20) * (v 3)) * (X m 11 ((v 13) * (v 7)) * (X m 15 ((v 21) * ((v 2) ^ 2)) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 ((v 14) + ((v 2) * (v 21))) * (X m 9 ((v 15) + ((v 3) * ((v 20) ^ 2))) * (X m 14 (v 8) * (X m 15 (v 9) * (1))))))))))))))))))))) =
      X m 4 (v 16) * (X m 5 (v 17) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 ((v 10) + ((v 12) * (v 6)) + ((v 21) * (v 3))) * (X m 11 ((v 11) + ((v 13) * (v 7)) + ((v 2) * (v 20))) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 8) + ((v 20) * (v 3))) * (X m 15 ((v 21) * ((v 2) ^ 2)) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 15 (v 9) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 ((v 14) + ((v 2) * (v 21))) * (X m 9 ((v 15) + ((v 3) * ((v 20) ^ 2))) * (1))))))))))))))))))) := by
  rw [(c_14_11 m ((v 20) * (v 3)) ((v 13) * (v 7))).left_comm]
  rw [(c_13_11 m (v 7) ((v 13) * (v 7))).left_comm]
  rw [(c_12_11 m (v 6) ((v 13) * (v 7))).left_comm]
  rw [(c_3_11 m (v 21) ((v 13) * (v 7))).left_comm]
  rw [(c_2_11 m (v 20) ((v 13) * (v 7))).left_comm]
  rw [add_suffix m 11 ((v 11) + ((v 2) * (v 20))) ((v 13) * (v 7)),
    show ((v 11) + ((v 2) * (v 20))) + ((v 13) * (v 7)) = ((v 11) + ((v 13) * (v 7)) + ((v 2) * (v 20))) by ring]
  rw [(c_9_14 m ((v 15) + ((v 3) * ((v 20) ^ 2))) (v 8)).left_comm]
  rw [(c_8_14 m ((v 14) + ((v 2) * (v 21))) (v 8)).left_comm]
  rw [(c_7_14 m (v 13) (v 8)).left_comm]
  rw [(c_6_14 m (v 12) (v 8)).left_comm]
  rw [(c_21_14 m (v 3) (v 8)).left_comm]
  rw [(c_20_14 m (v 2) (v 8)).left_comm]
  rw [(c_15_14 m ((v 21) * ((v 2) ^ 2)) (v 8)).left_comm]
  rw [add_suffix m 14 ((v 20) * (v 3)) (v 8),
    show ((v 20) * (v 3)) + (v 8) = ((v 8) + ((v 20) * (v 3))) by ring]
  rw [(c_9_15 m ((v 15) + ((v 3) * ((v 20) ^ 2))) (v 9)).left_comm]
  rw [(c_8_15 m ((v 14) + ((v 2) * (v 21))) (v 9)).left_comm]
  rw [(c_7_15 m (v 13) (v 9)).left_comm]
  rw [(c_6_15 m (v 12) (v 9)).left_comm]

private theorem chunk_5 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 16) * (X m 5 (v 17) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 ((v 10) + ((v 12) * (v 6)) + ((v 21) * (v 3))) * (X m 11 ((v 11) + ((v 13) * (v 7)) + ((v 2) * (v 20))) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 8) + ((v 20) * (v 3))) * (X m 15 ((v 21) * ((v 2) ^ 2)) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 15 (v 9) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 ((v 14) + ((v 2) * (v 21))) * (X m 9 ((v 15) + ((v 3) * ((v 20) ^ 2))) * (1))))))))))))))))))) =
      X m 4 (v 16) * (X m 5 (v 17) * (X m 16 (v 4) * (X m 17 (v 5) * (X m 10 ((v 10) + ((v 12) * (v 6)) + ((v 21) * (v 3))) * (X m 11 ((v 11) + ((v 13) * (v 7)) + ((v 2) * (v 20))) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 8) + ((v 20) * (v 3))) * (X m 15 ((v 9) + ((v 21) * ((v 2) ^ 2))) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 ((v 14) + ((v 2) * (v 21))) * (X m 9 ((v 15) + ((v 3) * ((v 20) ^ 2))) * (1)))))))))))))))))) := by
  rw [(c_21_15 m (v 3) (v 9)).left_comm]
  rw [(c_20_15 m (v 2) (v 9)).left_comm]
  rw [add_suffix m 15 ((v 21) * ((v 2) ^ 2)) (v 9),
    show ((v 21) * ((v 2) ^ 2)) + (v 9) = ((v 9) + ((v 21) * ((v 2) ^ 2))) by ring]

private theorem collected (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 4) * (X m 17 (v 5) * (X m 4 (v 16) * (X m 5 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 (v 14) * (X m 9 (v 15) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 (v 8) * (X m 15 (v 9) * (1)))))))))))))))))) =
      splitWord m ![0, 0, (v 20), (v 21), (v 16), (v 17), (v 12), (v 13), ((v 14) + ((v 2) * (v 21))), ((v 15) + ((v 3) * ((v 20) ^ 2))), ((v 10) + ((v 12) * (v 6)) + ((v 21) * (v 3))), ((v 11) + ((v 13) * (v 7)) + ((v 2) * (v 20))), (v 6), (v 7), ((v 8) + ((v 20) * (v 3))), ((v 9) + ((v 21) * ((v 2) ^ 2))), (v 4), (v 5), 0, 0, (v 2), (v 3), 0, 0] := by
  have h := (chunk_0 m v).trans ((chunk_1 m v).trans ((chunk_2 m v).trans ((chunk_3 m v).trans ((chunk_4 m v).trans ((chunk_5 m v))))))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk, xz, one_mul] using h

/-- Selected coordinates after the fixed linear reflection on D. -/
theorem coordinates (m : ℕ) (v q : Fin 24 → CoefficientField m)
    (he : X m 16 (v 4) * (X m 17 (v 5) * (X m 4 (v 16) * (X m 5 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 20 (v 2) * (X m 21 (v 3) * (X m 6 (v 12) * (X m 7 (v 13) * (X m 8 (v 14) * (X m 9 (v 15) * (X m 2 (v 20) * (X m 3 (v 21) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 (v 8) * (X m 15 (v 9) * (1)))))))))))))))))) = splitWord m q) :
    q 0 = 0 ∧ q 18 = 0 ∧ q 22 = 0 ∧ q 3 = (v 21) ∧ q 4 = (v 16) := by
  have hv := splitWord_injective m (he.symm.trans (collected m v))
  exact ⟨congrFun hv 0, congrFun hv 18, congrFun hv 22, congrFun hv 3, congrFun hv 4⟩

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2.WeylCollection
