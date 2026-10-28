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
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2.EighthCollection
open ReeF4.Parabolics ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
open ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination
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

private theorem c_2_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 16 b) :=
  xc m 2 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_2_17 (m : ℕ) (a b : CoefficientField m) :
    X m 2 a * X m 17 b = X m 17 b * X m 2 a * X m 8 (a*b) :=
  xs m 2 17 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_2_22 (m : ℕ) (a b : CoefficientField m) :
    X m 2 a * X m 22 b = X m 22 b * X m 2 a * X m 13 (a*b) * X m 4 (b*a^2) := by
  simpa only [mul_comm] using xb m 22 2 13 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem s_2_23 (m : ℕ) (a b : CoefficientField m) :
    X m 2 a * X m 23 b = X m 23 b * X m 2 a * X m 7 (a*b) :=
  xs m 2 23 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_3_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 5 b) :=
  xc m 3 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem s_3_22 (m : ℕ) (a b : CoefficientField m) :
    X m 3 a * X m 22 b = X m 22 b * X m 3 a * X m 6 (a*b) :=
  xs m 3 22 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_3_23 (m : ℕ) (a b : CoefficientField m) :
    X m 3 a * X m 23 b = X m 23 b * X m 3 a * X m 5 (a*b) * X m 12 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 3 23 5 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 5 (a*b)) (xx m 12 (a*b^2))
    (xc m 5 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem c_4_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 4 a) (X m 22 b) :=
  xc m 4 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_4_23 (m : ℕ) (a b : CoefficientField m) :
    X m 4 a * X m 23 b = X m 23 b * X m 4 a * X m 11 (a*b) * X m 16 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 4 23 11 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 11 (a*b)) (xx m 16 (a*b^2))
    (xc m 11 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem c_5_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 5 a) (X m 4 b) :=
  xc m 5 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_5_22 (m : ℕ) (a b : CoefficientField m) :
    X m 5 a * X m 22 b = X m 22 b * X m 5 a * X m 17 (a*b) * X m 10 (b*a^2) := by
  simpa only [mul_comm] using xb m 22 5 17 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_5_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 5 a) (X m 23 b) :=
  xc m 5 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 10 b) :=
  xc m 6 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_6_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 22 b) :=
  xc m 6 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_6_23 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 23 b = X m 23 b * X m 6 a * X m 17 (a*b) * X m 21 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 6 23 17 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 17 (a*b)) (xx m 21 (a*b^2))
    (xc m 17 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem c_7_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 3 b) :=
  xc m 7 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 5 b) :=
  xc m 7 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_7_6 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 6 b = X m 6 b * X m 7 a * X m 8 (a*b) * X m 9 (b*a^2) := by
  simpa only [mul_comm] using xb m 6 7 8 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

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

private theorem s_7_22 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 22 b = X m 22 b * X m 7 a * X m 20 (a*b) * X m 16 (b*a^2) := by
  simpa only [mul_comm] using xb m 22 7 20 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_7_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 23 b) :=
  xc m 7 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 3 b) :=
  xc m 8 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 6 b) :=
  xc m 8 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_7 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 7 b) :=
  xc m 8 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_8_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 17 b) :=
  xc m 8 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 20 b) :=
  xc m 8 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 21 b) :=
  xc m 8 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 22 b) :=
  xc m 8 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_8_23 (m : ℕ) (a b : CoefficientField m) :
    X m 8 a * X m 23 b = X m 23 b * X m 8 a * X m 14 (a*b) :=
  xs m 8 23 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

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

private theorem c_9_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 17 b) :=
  xc m 9 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 20 b) :=
  xc m 9 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 21 b) :=
  xc m 9 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_9_22 (m : ℕ) (a b : CoefficientField m) :
    X m 9 a * X m 22 b = X m 22 b * X m 9 a * X m 15 (a*b) :=
  xs m 9 22 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_9_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 23 b) :=
  xc m 9 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_12_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 16 b) :=
  xc m 12 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 17 b) :=
  xc m 12 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_12_22 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 22 b = X m 22 b * X m 12 a * X m 21 (a*b) :=
  xs m 12 22 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_12_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 23 b) :=
  xc m 12 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 3 b) :=
  xc m 13 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 4 b) :=
  xc m 13 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_13_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 22 b) :=
  xc m 13 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_13_23 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 23 b = X m 23 b * X m 13 a * X m 20 (a*b) :=
  xs m 13 23 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_14_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 10 b) :=
  xc m 14 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 13 b) :=
  xc m 14 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 16 b) :=
  xc m 14 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 17 b) :=
  xc m 14 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 22 b) :=
  xc m 14 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 23 b) :=
  xc m 14 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 10 b) :=
  xc m 15 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_15_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 22 b) :=
  xc m 15 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 23 b) :=
  xc m 15 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_16_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 16 a) (X m 4 b) :=
  xc m 16 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_16_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 16 a) (X m 5 b) :=
  xc m 16 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_16_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 16 a) (X m 22 b) :=
  xc m 16 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_16_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 16 a) (X m 23 b) :=
  xc m 16 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 4 b) :=
  xc m 17 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 5 b) :=
  xc m 17 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 16 b) :=
  xc m 17 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 22 b) :=
  xc m 17 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 23 b) :=
  xc m 17 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_20_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 22 b) :=
  xc m 20 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 23 b) :=
  xc m 20 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_21_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 22 b) :=
  xc m 21 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 23 b) :=
  xc m 21 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_23_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 23 a) (X m 22 b) :=
  xc m 23 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem chunk_0 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 22 (v 24) * (X m 23 (v 25) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 22 (v 24) * (X m 23 (v 25) * (1)))))))))))))))))))))) =
      X m 22 (v 24) * (X m 23 (v 25) * (X m 22 (v 24) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 17 ((v 24) * (v 5)) * (X m 10 ((v 24) * ((v 5) ^ 2)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 13 ((v 2) * (v 24)) * (X m 4 ((v 24) * ((v 2) ^ 2)) * (X m 3 (v 3) * (X m 6 ((v 24) * (v 3)) * (X m 12 (v 12) * (X m 21 ((v 12) * (v 24)) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 20 ((v 24) * (v 7)) * (X m 16 ((v 24) * ((v 7) ^ 2)) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 15 ((v 24) * (v 9)) * (X m 23 (v 25) * (1))))))))))))))))))))))))))))))) := by
  have h0 : X m 9 (v 9) * X m 22 (v 24) = X m 22 (v 24) * X m 9 (v 9) * X m 15 ((v 24) * (v 9)) := by
    have h := s_9_22 m (v 9) (v 24)
    rw [show (v 9) * (v 24) = ((v 24) * (v 9)) by ring] at h
    exact h
  rw [swap_suffix h0]
  rw [(c_8_22 m (v 8) (v 24)).left_comm]
  have h2 : X m 7 (v 7) * X m 22 (v 24) = X m 22 (v 24) * X m 7 (v 7) * X m 20 ((v 24) * (v 7)) * X m 16 ((v 24) * ((v 7) ^ 2)) := by
    have h := s_7_22 m (v 7) (v 24)
    rw [show (v 7) * (v 24) = ((v 24) * (v 7)) by ring, show (v 24) * (v 7) ^ 2 = ((v 24) * ((v 7) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h2]
  rw [(c_6_22 m (v 6) (v 24)).left_comm]
  rw [(c_21_22 m (v 21) (v 24)).left_comm]
  rw [(c_20_22 m (v 20) (v 24)).left_comm]
  rw [(c_15_22 m (v 15) (v 24)).left_comm]
  rw [(c_14_22 m (v 14) (v 24)).left_comm]
  rw [(c_13_22 m (v 13) (v 24)).left_comm]
  have h9 : X m 12 (v 12) * X m 22 (v 24) = X m 22 (v 24) * X m 12 (v 12) * X m 21 ((v 12) * (v 24)) := by
    have h := s_12_22 m (v 12) (v 24)
    rw [show (v 12) * (v 24) = ((v 12) * (v 24)) by ring] at h
    exact h
  rw [swap_suffix h9]
  have h10 : X m 3 (v 3) * X m 22 (v 24) = X m 22 (v 24) * X m 3 (v 3) * X m 6 ((v 24) * (v 3)) := by
    have h := s_3_22 m (v 3) (v 24)
    rw [show (v 3) * (v 24) = ((v 24) * (v 3)) by ring] at h
    exact h
  rw [swap_suffix h10]
  have h11 : X m 2 (v 2) * X m 22 (v 24) = X m 22 (v 24) * X m 2 (v 2) * X m 13 ((v 2) * (v 24)) * X m 4 ((v 24) * ((v 2) ^ 2)) := by
    have h := s_2_22 m (v 2) (v 24)
    rw [show (v 2) * (v 24) = ((v 2) * (v 24)) by ring, show (v 24) * (v 2) ^ 2 = ((v 24) * ((v 2) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h11]
  rw [(c_11_22 m (v 11) (v 24)).left_comm]
  rw [(c_10_22 m (v 10) (v 24)).left_comm]
  rw [(c_17_22 m (v 17) (v 24)).left_comm]
  rw [(c_16_22 m (v 16) (v 24)).left_comm]
  have h16 : X m 5 (v 5) * X m 22 (v 24) = X m 22 (v 24) * X m 5 (v 5) * X m 17 ((v 24) * (v 5)) * X m 10 ((v 24) * ((v 5) ^ 2)) := by
    have h := s_5_22 m (v 5) (v 24)
    rw [show (v 5) * (v 24) = ((v 24) * (v 5)) by ring, show (v 24) * (v 5) ^ 2 = ((v 24) * ((v 5) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h16]
  rw [(c_4_22 m (v 4) (v 24)).left_comm]

private theorem chunk_1 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 22 (v 24) * (X m 23 (v 25) * (X m 22 (v 24) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 17 ((v 24) * (v 5)) * (X m 10 ((v 24) * ((v 5) ^ 2)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 13 ((v 2) * (v 24)) * (X m 4 ((v 24) * ((v 2) ^ 2)) * (X m 3 (v 3) * (X m 6 ((v 24) * (v 3)) * (X m 12 (v 12) * (X m 21 ((v 12) * (v 24)) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 20 ((v 24) * (v 7)) * (X m 16 ((v 24) * ((v 7) ^ 2)) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 15 ((v 24) * (v 9)) * (X m 23 (v 25) * (1))))))))))))))))))))))))))))))) =
      X m 23 (v 25) * (X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2))) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 ((v 2) * (v 24)) * (X m 14 ((v 12) * (v 2) * (v 24)) * (X m 15 ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) * (X m 6 ((v 24) * (v 3)) * (X m 10 ((v 12) * (v 24) * (v 3)) * (X m 21 ((v 12) * (v 24)) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 20 ((v 24) * (v 7)) * (X m 16 ((v 24) * ((v 7) ^ 2)) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 15 ((v 24) * (v 9)) * (X m 23 (v 25) * (1))))))))))))))))))))))))))))) := by
  rw [(c_23_22 m (v 25) (v 24)).left_comm]
  rw [add_suffix m 22 (v 24) (v 24),
    show (v 24) + (v 24) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_10_16 m ((v 24) * ((v 5) ^ 2)) (v 16)).left_comm]
  rw [(c_17_16 m ((v 24) * (v 5)) (v 16)).left_comm]
  rw [(c_10_17 m ((v 24) * ((v 5) ^ 2)) (v 17)).left_comm]
  rw [add_suffix m 17 ((v 24) * (v 5)) (v 17),
    show ((v 24) * (v 5)) + (v 17) = ((v 17) + ((v 24) * (v 5))) by ring]
  rw [add_suffix m 10 ((v 24) * ((v 5) ^ 2)) (v 10),
    show ((v 24) * ((v 5) ^ 2)) + (v 10) = ((v 10) + ((v 24) * ((v 5) ^ 2))) by ring]
  rw [(c_13_4 m ((v 2) * (v 24)) ((v 24) * ((v 2) ^ 2))).left_comm]
  rw [(c_2_4 m (v 2) ((v 24) * ((v 2) ^ 2))).left_comm]
  rw [(c_11_4 m (v 11) ((v 24) * ((v 2) ^ 2))).left_comm]
  rw [(c_10_4 m ((v 10) + ((v 24) * ((v 5) ^ 2))) ((v 24) * ((v 2) ^ 2))).left_comm]
  rw [(c_17_4 m ((v 17) + ((v 24) * (v 5))) ((v 24) * ((v 2) ^ 2))).left_comm]
  rw [(c_16_4 m (v 16) ((v 24) * ((v 2) ^ 2))).left_comm]
  rw [(c_5_4 m (v 5) ((v 24) * ((v 2) ^ 2))).left_comm]
  rw [add_suffix m 4 (v 4) ((v 24) * ((v 2) ^ 2)),
    show (v 4) + ((v 24) * ((v 2) ^ 2)) = ((v 4) + ((v 24) * ((v 2) ^ 2))) by ring]
  rw [(c_13_3 m ((v 2) * (v 24)) (v 3)).left_comm]
  have h16 : X m 6 ((v 24) * (v 3)) * X m 12 (v 12) = X m 12 (v 12) * X m 6 ((v 24) * (v 3)) * X m 10 ((v 12) * (v 24) * (v 3)) := by
    have h := s_6_12 m ((v 24) * (v 3)) (v 12)
    rw [show ((v 24) * (v 3)) * (v 12) = ((v 12) * (v 24) * (v 3)) by ring] at h
    exact h
  rw [swap_suffix h16]
  have h17 : X m 13 ((v 2) * (v 24)) * X m 12 (v 12) = X m 12 (v 12) * X m 13 ((v 2) * (v 24)) * X m 14 ((v 12) * (v 2) * (v 24)) * X m 15 ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) := by
    have h := s_13_12 m ((v 2) * (v 24)) (v 12)
    rw [show ((v 2) * (v 24)) * (v 12) = ((v 12) * (v 2) * (v 24)) by ring, show (v 12) * ((v 2) * (v 24)) ^ 2 = ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h17]

private theorem chunk_2 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 23 (v 25) * (X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2))) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 ((v 2) * (v 24)) * (X m 14 ((v 12) * (v 2) * (v 24)) * (X m 15 ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) * (X m 6 ((v 24) * (v 3)) * (X m 10 ((v 12) * (v 24) * (v 3)) * (X m 21 ((v 12) * (v 24)) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 20 ((v 24) * (v 7)) * (X m 16 ((v 24) * ((v 7) ^ 2)) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 15 ((v 24) * (v 9)) * (X m 23 (v 25) * (1))))))))))))))))))))))))))))) =
      X m 23 (v 25) * (X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 12) * (v 2) * (v 24)) * (X m 14 (v 14) * (X m 15 ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) * (X m 21 ((v 12) * (v 24)) * (X m 6 ((v 24) * (v 3)) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 20 ((v 24) * (v 7)) * (X m 16 ((v 24) * ((v 7) ^ 2)) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 15 ((v 24) * (v 9)) * (X m 23 (v 25) * (1))))))))))))))))))))))))))) := by
  rw [(c_6_10 m ((v 24) * (v 3)) ((v 12) * (v 24) * (v 3))).left_comm]
  rw [(c_15_10 m ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) ((v 12) * (v 24) * (v 3))).left_comm]
  rw [(c_14_10 m ((v 12) * (v 2) * (v 24)) ((v 12) * (v 24) * (v 3))).left_comm]
  rw [(c_13_10 m ((v 2) * (v 24)) ((v 12) * (v 24) * (v 3))).left_comm]
  rw [(c_12_10 m (v 12) ((v 12) * (v 24) * (v 3))).left_comm]
  rw [(c_3_10 m (v 3) ((v 12) * (v 24) * (v 3))).left_comm]
  rw [(c_2_10 m (v 2) ((v 12) * (v 24) * (v 3))).left_comm]
  rw [(c_11_10 m (v 11) ((v 12) * (v 24) * (v 3))).left_comm]
  rw [add_suffix m 10 ((v 10) + ((v 24) * ((v 5) ^ 2))) ((v 12) * (v 24) * (v 3)),
    show ((v 10) + ((v 24) * ((v 5) ^ 2))) + ((v 12) * (v 24) * (v 3)) = ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) by ring]
  rw [(c_6_21 m ((v 24) * (v 3)) ((v 12) * (v 24))).left_comm]
  rw [(c_6_13 m ((v 24) * (v 3)) (v 13)).left_comm]
  rw [(c_21_13 m ((v 12) * (v 24)) (v 13)).left_comm]
  rw [(c_15_13 m ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) (v 13)).left_comm]
  rw [(c_14_13 m ((v 12) * (v 2) * (v 24)) (v 13)).left_comm]
  rw [add_suffix m 13 ((v 2) * (v 24)) (v 13),
    show ((v 2) * (v 24)) + (v 13) = ((v 13) + ((v 2) * (v 24))) by ring]
  rw [(c_6_14 m ((v 24) * (v 3)) (v 14)).left_comm]
  rw [(c_21_14 m ((v 12) * (v 24)) (v 14)).left_comm]
  rw [(c_15_14 m ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) (v 14)).left_comm]

private theorem chunk_3 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 23 (v 25) * (X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 12) * (v 2) * (v 24)) * (X m 14 (v 14) * (X m 15 ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) * (X m 21 ((v 12) * (v 24)) * (X m 6 ((v 24) * (v 3)) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 20 ((v 24) * (v 7)) * (X m 16 ((v 24) * ((v 7) ^ 2)) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 15 ((v 24) * (v 9)) * (X m 23 (v 25) * (1))))))))))))))))))))))))))) =
      X m 23 (v 25) * (X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 16 ((v 24) * ((v 7) ^ 2)) * (X m 15 ((v 15) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2))) * (X m 20 ((v 20) + ((v 24) * (v 7))) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 15 (((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 15 ((v 24) * (v 9)) * (X m 23 (v 25) * (1))))))))))))))))))))))) := by
  rw [add_suffix m 14 ((v 12) * (v 2) * (v 24)) (v 14),
    show ((v 12) * (v 2) * (v 24)) + (v 14) = ((v 14) + ((v 12) * (v 2) * (v 24))) by ring]
  rw [(c_6_15 m ((v 24) * (v 3)) (v 15)).left_comm]
  rw [(c_21_15 m ((v 12) * (v 24)) (v 15)).left_comm]
  rw [add_suffix m 15 ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) (v 15),
    show ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + (v 15) = ((v 15) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2))) by ring]
  rw [(c_6_20 m ((v 24) * (v 3)) (v 20)).left_comm]
  rw [(c_21_20 m ((v 12) * (v 24)) (v 20)).left_comm]
  rw [(c_6_21 m ((v 24) * (v 3)) (v 21)).left_comm]
  rw [add_suffix m 21 ((v 12) * (v 24)) (v 21),
    show ((v 12) * (v 24)) + (v 21) = ((v 21) + ((v 12) * (v 24))) by ring]
  rw [add_suffix m 6 ((v 24) * (v 3)) (v 6),
    show ((v 24) * (v 3)) + (v 6) = ((v 6) + ((v 24) * (v 3))) by ring]
  rw [(c_7_20 m (v 7) ((v 24) * (v 7))).left_comm]
  rw [(c_6_20 m ((v 6) + ((v 24) * (v 3))) ((v 24) * (v 7))).left_comm]
  rw [(c_21_20 m ((v 21) + ((v 12) * (v 24))) ((v 24) * (v 7))).left_comm]
  rw [add_suffix m 20 (v 20) ((v 24) * (v 7)),
    show (v 20) + ((v 24) * (v 7)) = ((v 20) + ((v 24) * (v 7))) by ring]
  rw [(c_7_16 m (v 7) ((v 24) * ((v 7) ^ 2))).left_comm]
  have h14 : X m 6 ((v 6) + ((v 24) * (v 3))) * X m 16 ((v 24) * ((v 7) ^ 2)) = X m 16 ((v 24) * ((v 7) ^ 2)) * X m 6 ((v 6) + ((v 24) * (v 3))) * X m 15 (((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) := by
    have h := s_6_16 m ((v 6) + ((v 24) * (v 3))) ((v 24) * ((v 7) ^ 2))
    rw [show ((v 6) + ((v 24) * (v 3))) * ((v 24) * ((v 7) ^ 2)) = (((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) by ring] at h
    exact h
  rw [swap_suffix h14]
  rw [(c_21_16 m ((v 21) + ((v 12) * (v 24))) ((v 24) * ((v 7) ^ 2))).left_comm]
  rw [(c_20_16 m ((v 20) + ((v 24) * (v 7))) ((v 24) * ((v 7) ^ 2))).left_comm]
  rw [(c_15_16 m ((v 15) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2))) ((v 24) * ((v 7) ^ 2))).left_comm]

private theorem chunk_4 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 23 (v 25) * (X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 16 ((v 24) * ((v 7) ^ 2)) * (X m 15 ((v 15) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2))) * (X m 20 ((v 20) + ((v 24) * (v 7))) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 15 (((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 15 ((v 24) * (v 9)) * (X m 23 (v 25) * (1))))))))))))))))))))))) =
      X m 23 (v 25) * (X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 (v 5) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 15 ((v 15) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2))) * (X m 20 ((v 20) + ((v 24) * (v 7))) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 15 (((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 9 ((v 24) * (v 3) * ((v 7) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 15 ((v 24) * (v 9)) * (X m 23 (v 25) * (1))))))))))))))))))))))) := by
  rw [(c_14_16 m ((v 14) + ((v 12) * (v 2) * (v 24))) ((v 24) * ((v 7) ^ 2))).left_comm]
  rw [(c_13_16 m ((v 13) + ((v 2) * (v 24))) ((v 24) * ((v 7) ^ 2))).left_comm]
  rw [(c_12_16 m (v 12) ((v 24) * ((v 7) ^ 2))).left_comm]
  have h3 : X m 3 (v 3) * X m 16 ((v 24) * ((v 7) ^ 2)) = X m 16 ((v 24) * ((v 7) ^ 2)) * X m 3 (v 3) * X m 9 ((v 24) * (v 3) * ((v 7) ^ 2)) := by
    have h := s_3_16 m (v 3) ((v 24) * ((v 7) ^ 2))
    rw [show (v 3) * ((v 24) * ((v 7) ^ 2)) = ((v 24) * (v 3) * ((v 7) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix h3]
  rw [(c_2_16 m (v 2) ((v 24) * ((v 7) ^ 2))).left_comm]
  rw [(c_11_16 m (v 11) ((v 24) * ((v 7) ^ 2))).left_comm]
  rw [(c_10_16 m ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) ((v 24) * ((v 7) ^ 2))).left_comm]
  rw [(c_17_16 m ((v 17) + ((v 24) * (v 5))) ((v 24) * ((v 7) ^ 2))).left_comm]
  rw [add_suffix m 16 (v 16) ((v 24) * ((v 7) ^ 2)),
    show (v 16) + ((v 24) * ((v 7) ^ 2)) = ((v 16) + ((v 24) * ((v 7) ^ 2))) by ring]
  rw [(c_9_12 m ((v 24) * (v 3) * ((v 7) ^ 2)) (v 12)).left_comm]
  rw [(c_9_13 m ((v 24) * (v 3) * ((v 7) ^ 2)) ((v 13) + ((v 2) * (v 24)))).left_comm]
  rw [(c_9_14 m ((v 24) * (v 3) * ((v 7) ^ 2)) ((v 14) + ((v 12) * (v 2) * (v 24)))).left_comm]
  rw [(c_9_15 m ((v 24) * (v 3) * ((v 7) ^ 2)) ((v 15) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)))).left_comm]
  rw [(c_9_20 m ((v 24) * (v 3) * ((v 7) ^ 2)) ((v 20) + ((v 24) * (v 7)))).left_comm]
  rw [(c_9_21 m ((v 24) * (v 3) * ((v 7) ^ 2)) ((v 21) + ((v 12) * (v 24)))).left_comm]
  rw [(c_9_6 m ((v 24) * (v 3) * ((v 7) ^ 2)) ((v 6) + ((v 24) * (v 3)))).left_comm]
  rw [(c_9_15 m ((v 24) * (v 3) * ((v 7) ^ 2)) (((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2)))).left_comm]
  rw [(c_6_15 m ((v 6) + ((v 24) * (v 3))) (((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2)))).left_comm]

private theorem chunk_5 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 23 (v 25) * (X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 (v 5) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 15 ((v 15) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2))) * (X m 20 ((v 20) + ((v 24) * (v 7))) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 15 (((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 9 ((v 24) * (v 3) * ((v 7) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 15 ((v 24) * (v 9)) * (X m 23 (v 25) * (1))))))))))))))))))))))) =
      X m 23 (v 25) * (X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 (v 5) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 24) * (v 7))) * (X m 23 (v 25) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 21 (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 14 ((v 25) * (v 8)) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) * (1))))))))))))))))))))))) := by
  rw [(c_21_15 m ((v 21) + ((v 12) * (v 24))) (((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2)))).left_comm]
  rw [(c_20_15 m ((v 20) + ((v 24) * (v 7))) (((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2)))).left_comm]
  rw [add_suffix m 15 ((v 15) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2))) (((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))),
    show ((v 15) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2))) + (((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) = ((v 15) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) by ring]
  rw [(c_9_7 m ((v 24) * (v 3) * ((v 7) ^ 2)) (v 7)).left_comm]
  rw [(c_9_8 m ((v 24) * (v 3) * ((v 7) ^ 2)) (v 8)).left_comm]
  rw [add_suffix m 9 ((v 24) * (v 3) * ((v 7) ^ 2)) (v 9),
    show ((v 24) * (v 3) * ((v 7) ^ 2)) + (v 9) = ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) by ring]
  rw [(c_9_15 m ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) ((v 24) * (v 9))).left_comm]
  rw [(c_8_15 m (v 8) ((v 24) * (v 9))).left_comm]
  rw [(c_7_15 m (v 7) ((v 24) * (v 9))).left_comm]
  rw [(c_6_15 m ((v 6) + ((v 24) * (v 3))) ((v 24) * (v 9))).left_comm]
  rw [(c_21_15 m ((v 21) + ((v 12) * (v 24))) ((v 24) * (v 9))).left_comm]
  rw [(c_20_15 m ((v 20) + ((v 24) * (v 7))) ((v 24) * (v 9))).left_comm]
  rw [add_suffix m 15 ((v 15) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) ((v 24) * (v 9)),
    show ((v 15) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) + ((v 24) * (v 9)) = ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) by ring]
  rw [(c_9_23 m ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) (v 25)).left_comm]
  have h14 : X m 8 (v 8) * X m 23 (v 25) = X m 23 (v 25) * X m 8 (v 8) * X m 14 ((v 25) * (v 8)) := by
    have h := s_8_23 m (v 8) (v 25)
    rw [show (v 8) * (v 25) = ((v 25) * (v 8)) by ring] at h
    exact h
  rw [swap_suffix h14]
  rw [(c_7_23 m (v 7) (v 25)).left_comm]
  have h16 : X m 6 ((v 6) + ((v 24) * (v 3))) * X m 23 (v 25) = X m 23 (v 25) * X m 6 ((v 6) + ((v 24) * (v 3))) * X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * X m 21 (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) := by
    have h := s_6_23 m ((v 6) + ((v 24) * (v 3))) (v 25)
    rw [show ((v 6) + ((v 24) * (v 3))) * (v 25) = (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) by ring, show ((v 6) + ((v 24) * (v 3))) * (v 25) ^ 2 = (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) by ring] at h
    exact h
  rw [swap_suffix_two h16]
  rw [(c_21_23 m ((v 21) + ((v 12) * (v 24))) (v 25)).left_comm]

private theorem chunk_6 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 23 (v 25) * (X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 (v 5) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 24) * (v 7))) * (X m 23 (v 25) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 21 (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 14 ((v 25) * (v 8)) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) * (1))))))))))))))))))))))) =
      X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 (v 5) * (X m 16 (((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2))) * (X m 11 (((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 7 ((v 2) * (v 25)) * (X m 3 (v 3) * (X m 5 ((v 25) * (v 3)) * (X m 12 ((v 3) * ((v 25) ^ 2)) * (X m 12 (v 12) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 20 (((v 13) * (v 25)) + ((v 2) * (v 24) * (v 25))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 24) * (v 7))) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 21 (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 14 ((v 25) * (v 8)) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) * (1))))))))))))))))))))))))))) := by
  rw [(c_20_23 m ((v 20) + ((v 24) * (v 7))) (v 25)).left_comm]
  rw [(c_15_23 m ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) (v 25)).left_comm]
  rw [(c_14_23 m ((v 14) + ((v 12) * (v 2) * (v 24))) (v 25)).left_comm]
  have h3 : X m 13 ((v 13) + ((v 2) * (v 24))) * X m 23 (v 25) = X m 23 (v 25) * X m 13 ((v 13) + ((v 2) * (v 24))) * X m 20 (((v 13) * (v 25)) + ((v 2) * (v 24) * (v 25))) := by
    have h := s_13_23 m ((v 13) + ((v 2) * (v 24))) (v 25)
    rw [show ((v 13) + ((v 2) * (v 24))) * (v 25) = (((v 13) * (v 25)) + ((v 2) * (v 24) * (v 25))) by ring] at h
    exact h
  rw [swap_suffix h3]
  rw [(c_12_23 m (v 12) (v 25)).left_comm]
  have h5 : X m 3 (v 3) * X m 23 (v 25) = X m 23 (v 25) * X m 3 (v 3) * X m 5 ((v 25) * (v 3)) * X m 12 ((v 3) * ((v 25) ^ 2)) := by
    have h := s_3_23 m (v 3) (v 25)
    rw [show (v 3) * (v 25) = ((v 25) * (v 3)) by ring, show (v 3) * (v 25) ^ 2 = ((v 3) * ((v 25) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h5]
  have h6 : X m 2 (v 2) * X m 23 (v 25) = X m 23 (v 25) * X m 2 (v 2) * X m 7 ((v 2) * (v 25)) := by
    have h := s_2_23 m (v 2) (v 25)
    rw [show (v 2) * (v 25) = ((v 2) * (v 25)) by ring] at h
    exact h
  rw [swap_suffix h6]
  rw [(c_11_23 m (v 11) (v 25)).left_comm]
  rw [(c_10_23 m ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) (v 25)).left_comm]
  rw [(c_17_23 m ((v 17) + ((v 24) * (v 5))) (v 25)).left_comm]
  rw [(c_16_23 m ((v 16) + ((v 24) * ((v 7) ^ 2))) (v 25)).left_comm]
  rw [(c_5_23 m (v 5) (v 25)).left_comm]
  have h12 : X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * X m 23 (v 25) = X m 23 (v 25) * X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * X m 11 (((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) * X m 16 (((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) := by
    have h := s_4_23 m ((v 4) + ((v 24) * ((v 2) ^ 2))) (v 25)
    rw [show ((v 4) + ((v 24) * ((v 2) ^ 2))) * (v 25) = (((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) by ring, show ((v 4) + ((v 24) * ((v 2) ^ 2))) * (v 25) ^ 2 = (((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) by ring] at h
    exact h
  rw [swap_suffix_two h12]
  rw [add_suffix m 23 (v 25) (v 25),
    show (v 25) + (v 25) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_11_16 m (((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) (((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2)))).left_comm]
  rw [(c_11_5 m (((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) (v 5)).left_comm]
  rw [(c_16_5 m (((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) (v 5)).left_comm]
  rw [(c_11_16 m (((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) ((v 16) + ((v 24) * ((v 7) ^ 2)))).left_comm]

private theorem chunk_7 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 (v 5) * (X m 16 (((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2))) * (X m 11 (((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 7 ((v 2) * (v 25)) * (X m 3 (v 3) * (X m 5 ((v 25) * (v 3)) * (X m 12 ((v 3) * ((v 25) ^ 2)) * (X m 12 (v 12) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 20 (((v 13) * (v 25)) + ((v 2) * (v 24) * (v 25))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 24) * (v 7))) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 21 (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 14 ((v 25) * (v 8)) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) * (1))))))))))))))))))))))))))) =
      X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 ((v 5) + ((v 25) * (v 3))) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2)) + ((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 ((v 11) + ((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 ((v 12) + ((v 3) * ((v 25) ^ 2))) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 11 (((v 13) * (v 2) * (v 25)) + ((v 24) * (v 25) * ((v 2) ^ 2))) * (X m 7 ((v 2) * (v 25)) * (X m 20 (((v 13) * (v 25)) + ((v 2) * (v 24) * (v 25))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 24) * (v 7))) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 21 (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 14 ((v 25) * (v 8)) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) * (1)))))))))))))))))))))))) := by
  rw [add_suffix m 16 (((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) ((v 16) + ((v 24) * ((v 7) ^ 2))),
    show (((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) + ((v 16) + ((v 24) * ((v 7) ^ 2))) = ((v 16) + ((v 24) * ((v 7) ^ 2)) + ((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) by ring]
  rw [(c_11_17 m (((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) ((v 17) + ((v 24) * (v 5)))).left_comm]
  rw [(c_11_10 m (((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3)))).left_comm]
  rw [add_suffix m 11 (((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) (v 11),
    show (((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) + (v 11) = ((v 11) + ((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) by ring]
  rw [(c_7_3 m ((v 2) * (v 25)) (v 3)).left_comm]
  rw [(c_7_5 m ((v 2) * (v 25)) ((v 25) * (v 3))).left_comm]
  rw [(c_3_5 m (v 3) ((v 25) * (v 3))).left_comm]
  rw [(c_2_5 m (v 2) ((v 25) * (v 3))).left_comm]
  rw [(c_11_5 m ((v 11) + ((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) ((v 25) * (v 3))).left_comm]
  rw [(c_10_5 m ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) ((v 25) * (v 3))).left_comm]
  rw [(c_17_5 m ((v 17) + ((v 24) * (v 5))) ((v 25) * (v 3))).left_comm]
  rw [(c_16_5 m ((v 16) + ((v 24) * ((v 7) ^ 2)) + ((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) ((v 25) * (v 3))).left_comm]
  rw [add_suffix m 5 (v 5) ((v 25) * (v 3)),
    show (v 5) + ((v 25) * (v 3)) = ((v 5) + ((v 25) * (v 3))) by ring]
  rw [(c_7_12 m ((v 2) * (v 25)) ((v 3) * ((v 25) ^ 2))).left_comm]
  rw [(c_7_12 m ((v 2) * (v 25)) (v 12)).left_comm]
  rw [add_suffix m 12 ((v 3) * ((v 25) ^ 2)) (v 12),
    show ((v 3) * ((v 25) ^ 2)) + (v 12) = ((v 12) + ((v 3) * ((v 25) ^ 2))) by ring]
  have h16 : X m 7 ((v 2) * (v 25)) * X m 13 ((v 13) + ((v 2) * (v 24))) = X m 13 ((v 13) + ((v 2) * (v 24))) * X m 7 ((v 2) * (v 25)) * X m 11 (((v 13) * (v 2) * (v 25)) + ((v 24) * (v 25) * ((v 2) ^ 2))) := by
    have h := s_7_13 m ((v 2) * (v 25)) ((v 13) + ((v 2) * (v 24)))
    rw [show ((v 2) * (v 25)) * ((v 13) + ((v 2) * (v 24))) = (((v 13) * (v 2) * (v 25)) + ((v 24) * (v 25) * ((v 2) ^ 2))) by ring] at h
    exact h
  rw [swap_suffix h16]
  rw [(c_7_11 m ((v 2) * (v 25)) (((v 13) * (v 2) * (v 25)) + ((v 24) * (v 25) * ((v 2) ^ 2)))).left_comm]

private theorem chunk_8 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 ((v 5) + ((v 25) * (v 3))) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2)) + ((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 ((v 11) + ((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 ((v 12) + ((v 3) * ((v 25) ^ 2))) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 11 (((v 13) * (v 2) * (v 25)) + ((v 24) * (v 25) * ((v 2) ^ 2))) * (X m 7 ((v 2) * (v 25)) * (X m 20 (((v 13) * (v 25)) + ((v 2) * (v 24) * (v 25))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 24) * (v 7))) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 21 (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 14 ((v 25) * (v 8)) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) * (1)))))))))))))))))))))))) =
      X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 ((v 5) + ((v 25) * (v 3))) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2)) + ((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 ((v 11) + ((v 25) * (v 4)) + ((v 13) * (v 2) * (v 25))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 ((v 12) + ((v 3) * ((v 25) ^ 2))) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25))) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 7 ((v 2) * (v 25)) * (X m 14 (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) * (X m 8 (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) * (X m 9 (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 21 (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 14 ((v 25) * (v 8)) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) * (1))))))))))))))))))))))))) := by
  rw [(c_13_11 m ((v 13) + ((v 2) * (v 24))) (((v 13) * (v 2) * (v 25)) + ((v 24) * (v 25) * ((v 2) ^ 2)))).left_comm]
  rw [(c_12_11 m ((v 12) + ((v 3) * ((v 25) ^ 2))) (((v 13) * (v 2) * (v 25)) + ((v 24) * (v 25) * ((v 2) ^ 2)))).left_comm]
  rw [(c_3_11 m (v 3) (((v 13) * (v 2) * (v 25)) + ((v 24) * (v 25) * ((v 2) ^ 2)))).left_comm]
  rw [(c_2_11 m (v 2) (((v 13) * (v 2) * (v 25)) + ((v 24) * (v 25) * ((v 2) ^ 2)))).left_comm]
  rw [add_suffix m 11 ((v 11) + ((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) (((v 13) * (v 2) * (v 25)) + ((v 24) * (v 25) * ((v 2) ^ 2))),
    show ((v 11) + ((v 25) * (v 4)) + ((v 24) * (v 25) * ((v 2) ^ 2))) + (((v 13) * (v 2) * (v 25)) + ((v 24) * (v 25) * ((v 2) ^ 2))) = ((v 11) + ((v 25) * (v 4)) + ((v 13) * (v 2) * (v 25))) by ring_nf; simp [CharTwo.two_eq_zero]]
  rw [(c_7_20 m ((v 2) * (v 25)) (((v 13) * (v 25)) + ((v 2) * (v 24) * (v 25)))).left_comm]
  rw [(c_7_14 m ((v 2) * (v 25)) ((v 14) + ((v 12) * (v 2) * (v 24)))).left_comm]
  rw [(c_20_14 m (((v 13) * (v 25)) + ((v 2) * (v 24) * (v 25))) ((v 14) + ((v 12) * (v 2) * (v 24)))).left_comm]
  rw [(c_7_15 m ((v 2) * (v 25)) ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2)))).left_comm]
  rw [(c_20_15 m (((v 13) * (v 25)) + ((v 2) * (v 24) * (v 25))) ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2)))).left_comm]
  rw [(c_7_20 m ((v 2) * (v 25)) ((v 20) + ((v 24) * (v 7)))).left_comm]
  rw [add_suffix m 20 (((v 13) * (v 25)) + ((v 2) * (v 24) * (v 25))) ((v 20) + ((v 24) * (v 7))),
    show (((v 13) * (v 25)) + ((v 2) * (v 24) * (v 25))) + ((v 20) + ((v 24) * (v 7))) = ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25))) by ring]
  rw [(c_7_21 m ((v 2) * (v 25)) ((v 21) + ((v 12) * (v 24)))).left_comm]
  have h13 : X m 7 ((v 2) * (v 25)) * X m 6 ((v 6) + ((v 24) * (v 3))) = X m 6 ((v 6) + ((v 24) * (v 3))) * X m 7 ((v 2) * (v 25)) * X m 8 (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) * X m 9 (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) := by
    have h := s_7_6 m ((v 2) * (v 25)) ((v 6) + ((v 24) * (v 3)))
    rw [show ((v 2) * (v 25)) * ((v 6) + ((v 24) * (v 3))) = (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) by ring, show ((v 6) + ((v 24) * (v 3))) * ((v 2) * (v 25)) ^ 2 = (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) by ring] at h
    exact h
  rw [swap_suffix_two h13]
  rw [(c_9_17 m (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))).left_comm]
  rw [(c_8_17 m (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))).left_comm]
  have h16 : X m 7 ((v 2) * (v 25)) * X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) = X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * X m 7 ((v 2) * (v 25)) * X m 14 (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) := by
    have h := s_7_17 m ((v 2) * (v 25)) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))
    rw [show ((v 2) * (v 25)) * (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) = (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) by ring] at h
    exact h
  rw [swap_suffix h16]
  rw [(c_6_17 m ((v 6) + ((v 24) * (v 3))) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))).left_comm]

private theorem chunk_9 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 ((v 5) + ((v 25) * (v 3))) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2)) + ((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 ((v 11) + ((v 25) * (v 4)) + ((v 13) * (v 2) * (v 25))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 ((v 12) + ((v 3) * ((v 25) ^ 2))) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25))) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 7 ((v 2) * (v 25)) * (X m 14 (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) * (X m 8 (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) * (X m 9 (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 21 (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 14 ((v 25) * (v 8)) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) * (1))))))))))))))))))))))))) =
      X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 ((v 5) + ((v 25) * (v 3))) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2)) + ((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5)) + ((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 ((v 11) + ((v 25) * (v 4)) + ((v 13) * (v 2) * (v 25))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 ((v 12) + ((v 3) * ((v 25) ^ 2))) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25))) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 8 (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 7 ((v 2) * (v 25)) * (X m 14 (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) * (X m 8 (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) * (X m 9 (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 21 (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 14 ((v 25) * (v 8)) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) * (1))))))))))))))))))))))))) := by
  rw [(c_21_17 m ((v 21) + ((v 12) * (v 24))) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))).left_comm]
  rw [(c_20_17 m ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25))) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))).left_comm]
  rw [(c_15_17 m ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))).left_comm]
  rw [(c_14_17 m ((v 14) + ((v 12) * (v 2) * (v 24))) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))).left_comm]
  rw [(c_13_17 m ((v 13) + ((v 2) * (v 24))) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))).left_comm]
  rw [(c_12_17 m ((v 12) + ((v 3) * ((v 25) ^ 2))) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))).left_comm]
  rw [(c_3_17 m (v 3) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))).left_comm]
  have h7 : X m 2 (v 2) * X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) = X m 17 (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * X m 2 (v 2) * X m 8 (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) := by
    have h := s_2_17 m (v 2) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))
    rw [show (v 2) * (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) = (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) by ring] at h
    exact h
  rw [swap_suffix h7]
  rw [(c_11_17 m ((v 11) + ((v 25) * (v 4)) + ((v 13) * (v 2) * (v 25))) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))).left_comm]
  rw [(c_10_17 m ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3)))).left_comm]
  rw [add_suffix m 17 ((v 17) + ((v 24) * (v 5))) (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))),
    show ((v 17) + ((v 24) * (v 5))) + (((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) = ((v 17) + ((v 24) * (v 5)) + ((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) by ring]
  rw [(c_8_3 m (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) (v 3)).left_comm]
  rw [(c_8_12 m (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) ((v 12) + ((v 3) * ((v 25) ^ 2)))).left_comm]
  rw [(c_8_13 m (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) ((v 13) + ((v 2) * (v 24)))).left_comm]
  rw [(c_8_14 m (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) ((v 14) + ((v 12) * (v 2) * (v 24)))).left_comm]
  rw [(c_8_15 m (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2)))).left_comm]
  rw [(c_8_20 m (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25)))).left_comm]
  rw [(c_8_21 m (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) ((v 21) + ((v 12) * (v 24)))).left_comm]

private theorem chunk_10 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 ((v 5) + ((v 25) * (v 3))) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2)) + ((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5)) + ((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 ((v 11) + ((v 25) * (v 4)) + ((v 13) * (v 2) * (v 25))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 ((v 12) + ((v 3) * ((v 25) ^ 2))) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25))) * (X m 21 ((v 21) + ((v 12) * (v 24))) * (X m 8 (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 7 ((v 2) * (v 25)) * (X m 14 (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) * (X m 8 (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) * (X m 9 (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 21 (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 14 ((v 25) * (v 8)) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) * (1))))))))))))))))))))))))) =
      X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 ((v 5) + ((v 25) * (v 3))) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2)) + ((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5)) + ((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 ((v 11) + ((v 25) * (v 4)) + ((v 13) * (v 2) * (v 25))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 ((v 12) + ((v 3) * ((v 25) ^ 2))) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24)) + ((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25))) * (X m 21 ((v 21) + ((v 12) * (v 24)) + ((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 7 ((v 7) + ((v 2) * (v 25))) * (X m 8 (v 8) * (X m 14 ((v 25) * (v 8)) * (X m 9 (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) * (1)))))))))))))))))))) := by
  rw [(c_8_6 m (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) ((v 6) + ((v 24) * (v 3)))).left_comm]
  rw [(c_8_7 m (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) ((v 2) * (v 25))).left_comm]
  rw [(c_8_14 m (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2)))).left_comm]
  rw [(c_7_14 m ((v 2) * (v 25)) (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2)))).left_comm]
  rw [(c_6_14 m ((v 6) + ((v 24) * (v 3))) (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2)))).left_comm]
  rw [(c_21_14 m ((v 21) + ((v 12) * (v 24))) (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2)))).left_comm]
  rw [(c_20_14 m ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25))) (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2)))).left_comm]
  rw [(c_15_14 m ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2)))).left_comm]
  rw [add_suffix m 14 ((v 14) + ((v 12) * (v 2) * (v 24))) (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))),
    show ((v 14) + ((v 12) * (v 2) * (v 24))) + (((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) = ((v 14) + ((v 12) * (v 2) * (v 24)) + ((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) by ring]
  rw [add_suffix m 8 (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))),
    show (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) + (((v 2) * (v 25) * (v 6)) + ((v 2) * (v 24) * (v 25) * (v 3))) = 0 by ring_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  rw [(c_9_21 m (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2)))).left_comm]
  rw [(c_7_21 m ((v 2) * (v 25)) (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2)))).left_comm]
  rw [(c_6_21 m ((v 6) + ((v 24) * (v 3))) (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2)))).left_comm]
  rw [add_suffix m 21 ((v 21) + ((v 12) * (v 24))) (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))),
    show ((v 21) + ((v 12) * (v 24))) + (((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) = ((v 21) + ((v 12) * (v 24)) + ((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) by ring]
  rw [(c_9_7 m (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) (v 7)).left_comm]
  rw [add_suffix m 7 ((v 2) * (v 25)) (v 7),
    show ((v 2) * (v 25)) + (v 7) = ((v 7) + ((v 2) * (v 25))) by ring]
  rw [(c_9_8 m (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) (v 8)).left_comm]
  rw [(c_9_14 m (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) ((v 25) * (v 8))).left_comm]

private theorem chunk_11 (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 ((v 5) + ((v 25) * (v 3))) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2)) + ((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5)) + ((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 ((v 11) + ((v 25) * (v 4)) + ((v 13) * (v 2) * (v 25))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 ((v 12) + ((v 3) * ((v 25) ^ 2))) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 12) * (v 2) * (v 24)) + ((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25))) * (X m 21 ((v 21) + ((v 12) * (v 24)) + ((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 7 ((v 7) + ((v 2) * (v 25))) * (X m 8 (v 8) * (X m 14 ((v 25) * (v 8)) * (X m 9 (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) * (1)))))))))))))))))))) =
      X m 4 ((v 4) + ((v 24) * ((v 2) ^ 2))) * (X m 5 ((v 5) + ((v 25) * (v 3))) * (X m 16 ((v 16) + ((v 24) * ((v 7) ^ 2)) + ((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (X m 17 ((v 17) + ((v 24) * (v 5)) + ((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) * (X m 10 ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))) * (X m 11 ((v 11) + ((v 25) * (v 4)) + ((v 13) * (v 2) * (v 25))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 ((v 12) + ((v 3) * ((v 25) ^ 2))) * (X m 13 ((v 13) + ((v 2) * (v 24))) * (X m 14 ((v 14) + ((v 25) * (v 8)) + ((v 12) * (v 2) * (v 24)) + ((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) * (X m 15 ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) * (X m 20 ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25))) * (X m 21 ((v 21) + ((v 12) * (v 24)) + ((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) * (X m 6 ((v 6) + ((v 24) * (v 3))) * (X m 7 ((v 7) + ((v 2) * (v 25))) * (X m 8 (v 8) * (X m 9 ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2)) + ((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) * (1)))))))))))))))))) := by
  rw [(c_8_14 m (v 8) ((v 25) * (v 8))).left_comm]
  rw [(c_7_14 m ((v 7) + ((v 2) * (v 25))) ((v 25) * (v 8))).left_comm]
  rw [(c_6_14 m ((v 6) + ((v 24) * (v 3))) ((v 25) * (v 8))).left_comm]
  rw [(c_21_14 m ((v 21) + ((v 12) * (v 24)) + ((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) ((v 25) * (v 8))).left_comm]
  rw [(c_20_14 m ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25))) ((v 25) * (v 8))).left_comm]
  rw [(c_15_14 m ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))) ((v 25) * (v 8))).left_comm]
  rw [add_suffix m 14 ((v 14) + ((v 12) * (v 2) * (v 24)) + ((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) ((v 25) * (v 8)),
    show ((v 14) + ((v 12) * (v 2) * (v 24)) + ((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) + ((v 25) * (v 8)) = ((v 14) + ((v 25) * (v 8)) + ((v 12) * (v 2) * (v 24)) + ((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))) by ring]
  rw [add_suffix m 9 (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))),
    show (((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) + ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2))) = ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2)) + ((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))) by ring]

private theorem collected (m : ℕ) (v : Fin 26 → CoefficientField m) :
    X m 22 (v 24) * (X m 23 (v 25) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 22 (v 24) * (X m 23 (v 25) * (1)))))))))))))))))))))) =
      splitWord m ![0, 0, (v 2), (v 3), ((v 4) + ((v 24) * ((v 2) ^ 2))), ((v 5) + ((v 25) * (v 3))), ((v 6) + ((v 24) * (v 3))), ((v 7) + ((v 2) * (v 25))), (v 8), ((v 9) + ((v 24) * (v 3) * ((v 7) ^ 2)) + ((v 6) * ((v 2) ^ 2) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 2) ^ 2) * ((v 25) ^ 2))), ((v 10) + ((v 24) * ((v 5) ^ 2)) + ((v 12) * (v 24) * (v 3))), ((v 11) + ((v 25) * (v 4)) + ((v 13) * (v 2) * (v 25))), ((v 12) + ((v 3) * ((v 25) ^ 2))), ((v 13) + ((v 2) * (v 24))), ((v 14) + ((v 25) * (v 8)) + ((v 12) * (v 2) * (v 24)) + ((v 2) * (v 6) * ((v 25) ^ 2)) + ((v 2) * (v 24) * (v 3) * ((v 25) ^ 2))), ((v 15) + ((v 24) * (v 9)) + ((v 12) * ((v 2) ^ 2) * ((v 24) ^ 2)) + ((v 24) * (v 6) * ((v 7) ^ 2)) + ((v 3) * ((v 24) ^ 2) * ((v 7) ^ 2))), ((v 16) + ((v 24) * ((v 7) ^ 2)) + ((v 4) * ((v 25) ^ 2)) + ((v 24) * ((v 2) ^ 2) * ((v 25) ^ 2))), ((v 17) + ((v 24) * (v 5)) + ((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))), 0, 0, ((v 20) + ((v 13) * (v 25)) + ((v 24) * (v 7)) + ((v 2) * (v 24) * (v 25))), ((v 21) + ((v 12) * (v 24)) + ((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))), 0, 0] := by
  have h := (chunk_0 m v).trans ((chunk_1 m v).trans ((chunk_2 m v).trans ((chunk_3 m v).trans ((chunk_4 m v).trans ((chunk_5 m v).trans ((chunk_6 m v).trans ((chunk_7 m v).trans ((chunk_8 m v).trans ((chunk_9 m v).trans ((chunk_10 m v).trans ((chunk_11 m v))))))))))))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk, xz, one_mul] using h

/-- Selected coordinates of the eighth conjugate, in the established split order. -/
theorem coordinates (m : ℕ) (v : Fin 26 → CoefficientField m)
    (q : Fin 24 → CoefficientField m)
    (he : X m 22 (v 24) * (X m 23 (v 25) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 22 (v 24) * (X m 23 (v 25) * (1)))))))))))))))))))))) = splitWord m q) :
    q 0 = 0 ∧ q 18 = 0 ∧ q 22 = 0 ∧ q 3 = (v 3) ∧ q 6 = ((v 6) + ((v 24) * (v 3))) ∧ q 17 = ((v 17) + ((v 24) * (v 5)) + ((v 25) * (v 6)) + ((v 24) * (v 25) * (v 3))) ∧ q 21 = ((v 21) + ((v 12) * (v 24)) + ((v 6) * ((v 25) ^ 2)) + ((v 24) * (v 3) * ((v 25) ^ 2))) := by
  have hv := splitWord_injective m (he.symm.trans (collected m v))
  exact ⟨congrFun hv 0, congrFun hv 18, congrFun hv 22, congrFun hv 3, congrFun hv 6, congrFun hv 17, congrFun hv 21⟩

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2.EighthCollection
