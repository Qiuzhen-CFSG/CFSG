module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords
/-!
Split-root collection for conjugation of the five-coordinate involution tail.
This is the literal x₁(t)⁻¹ tail x₁(t) calculation, with half-Frobenius
parameters initially independent. Its consumer specializes them in `First`.
Each adjacent exchange is an instance of the actual split F₄ matrix relation;
the final coordinate comparison uses unique positive split coordinates.
Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/
public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.TailCompression
open NormalizedRootCentralizers.CenterExponent.OuterElimination
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

private theorem c_0_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 0 a) (X m 16 b) :=
  xc m 0 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_0_17 (m : ℕ) (a b : CoefficientField m) :
    X m 0 a * X m 17 b = X m 17 b * X m 0 a * X m 11 (a*b) * X m 15 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 0 17 11 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 11 (a*b)) (xx m 15 (a*b^2))
    (xc m 11 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem s_1_0 (m : ℕ) (a b : CoefficientField m) :
    X m 1 a * X m 0 b = X m 0 b * X m 1 a * X m 2 (a*b) * X m 3 (b*a^2) := by
  simpa only [mul_comm] using xb m 0 1 2 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_1_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 1 a) (X m 10 b) :=
  xc m 1 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_1_11 (m : ℕ) (a b : CoefficientField m) :
    X m 1 a * X m 11 b = X m 11 b * X m 1 a * X m 8 (a*b) :=
  xs m 1 11 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_1_16 (m : ℕ) (a b : CoefficientField m) :
    X m 1 a * X m 16 b = X m 16 b * X m 1 a * X m 14 (a*b) * X m 10 (b*a^2) := by
  simpa only [mul_comm] using xb m 16 1 14 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_1_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 1 a) (X m 17 b) :=
  xc m 1 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_2_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 0 b) :=
  xc m 2 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_2_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 1 b) :=
  xc m 2 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_2_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 16 b) :=
  xc m 2 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_2_17 (m : ℕ) (a b : CoefficientField m) :
    X m 2 a * X m 17 b = X m 17 b * X m 2 a * X m 8 (a*b) :=
  xs m 2 17 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_3_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 0 b) :=
  xc m 3 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_8_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 0 b) :=
  xc m 8 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 1 b) :=
  xc m 8 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 2 b) :=
  xc m 8 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 3 b) :=
  xc m 8 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_9_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 0 b) :=
  xc m 9 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 1 b) :=
  xc m 9 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 2 b) :=
  xc m 9 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 3 b) :=
  xc m 9 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_8 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 8 b) :=
  xc m 9 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 11 b) :=
  xc m 9 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_14_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 0 b) :=
  xc m 14 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 1 b) :=
  xc m 14 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_14_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 16 b) :=
  xc m 14 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 17 b) :=
  xc m 14 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 0 b) :=
  xc m 15 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 1 b) :=
  xc m 15 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 2 b) :=
  xc m 15 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_3 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 3 b) :=
  xc m 15 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 10 b) :=
  xc m 15 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 11 b) :=
  xc m 15 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_20_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 0 b) :=
  xc m 20 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_20_1 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 1 b = X m 1 b * X m 20 a * X m 17 (a*b) :=
  xs m 20 1 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_20_2 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 2 b = X m 2 b * X m 20 a * X m 11 (a*b) :=
  xs m 20 2 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_20_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 11 b) :=
  xc m 20 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 14 b) :=
  xc m 20 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 16 b) :=
  xc m 20 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 17 b) :=
  xc m 20 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_21_0 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 0 b = X m 0 b * X m 21 a * X m 16 (a*b) :=
  xs m 21 0 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_21_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 1 b) :=
  xc m 21 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_21_2 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 2 b = X m 2 b * X m 21 a * X m 14 (a*b) * X m 9 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 21 2 14 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 14 (a*b)) (xx m 9 (a*b^2))
    (xc m 14 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem c_21_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 14 b) :=
  xc m 21 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 16 b) :=
  xc m 21 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 20 b) :=
  xc m 21 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem first_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 2 ((v 10) * (v 11)) * (X m 1 (v 11) * (X m 0 (v 10) * (X m 16 (v 0) * (X m 17 (v 1) * (X m 10 (v 2) * (X m 11 (v 3) * (X m 15 (v 4) * (X m 14 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (X m 9 (v 8) * (X m 8 (v 9) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 2 ((v 10) * (v 11)) * (1)))))))))))))))) =
      X m 16 (v 0) * (X m 10 ((v 0) * ((v 11) ^ 2)) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 3 ((v 10) * ((v 11) ^ 2)) * (X m 14 ((v 0) * (v 11)) * (X m 17 (v 1) * (X m 10 (v 2) * (X m 11 (v 3) * (X m 15 (v 4) * (X m 14 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (X m 9 (v 8) * (X m 8 (v 9) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 2 ((v 10) * (v 11)) * (1)))))))))))))))))) := by
  rw [(c_2_1 m ((v 10) * (v 11)) (v 11)).left_comm]
  rw [(c_2_0 m ((v 10) * (v 11)) (v 10)).left_comm]
  have h2 : X m 1 (v 11) * X m 0 (v 10) = X m 0 (v 10) * X m 1 (v 11) * X m 2 ((v 10) * (v 11)) * X m 3 ((v 10) * ((v 11) ^ 2)) := by
    have h := s_1_0 m (v 11) (v 10)
    rw [show (v 11) * (v 10) = ((v 10) * (v 11)) by ring, show (v 10) * (v 11) ^ 2 = ((v 10) * ((v 11) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h2]
  rw [(c_3_2 m ((v 10) * ((v 11) ^ 2)) ((v 10) * (v 11))).left_comm]
  rw [add_suffix m 2 ((v 10) * (v 11)) ((v 10) * (v 11)),
    show ((v 10) * (v 11)) + ((v 10) * (v 11)) = 0 by ring_nf; simp only [CharTwo.two_eq_zero, mul_zero], xz, one_mul]
  have h5 : X m 3 ((v 10) * ((v 11) ^ 2)) * X m 16 (v 0) = X m 16 (v 0) * X m 3 ((v 10) * ((v 11) ^ 2)) * X m 9 ((v 0) * (v 10) * ((v 11) ^ 2)) := by
    have h := s_3_16 m ((v 10) * ((v 11) ^ 2)) (v 0)
    rw [show ((v 10) * ((v 11) ^ 2)) * (v 0) = ((v 0) * (v 10) * ((v 11) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix h5]
  have h6 : X m 1 (v 11) * X m 16 (v 0) = X m 16 (v 0) * X m 1 (v 11) * X m 14 ((v 0) * (v 11)) * X m 10 ((v 0) * ((v 11) ^ 2)) := by
    have h := s_1_16 m (v 11) (v 0)
    rw [show (v 11) * (v 0) = ((v 0) * (v 11)) by ring, show (v 0) * (v 11) ^ 2 = ((v 0) * ((v 11) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h6]
  rw [(c_0_16 m (v 10) (v 0)).left_comm]
  rw [(c_14_10 m ((v 0) * (v 11)) ((v 0) * ((v 11) ^ 2))).left_comm]
  rw [(c_1_10 m (v 11) ((v 0) * ((v 11) ^ 2))).left_comm]
  have h10 : X m 0 (v 10) * X m 10 ((v 0) * ((v 11) ^ 2)) = X m 10 ((v 0) * ((v 11) ^ 2)) * X m 0 (v 10) * X m 9 ((v 0) * (v 10) * ((v 11) ^ 2)) := by
    have h := s_0_10 m (v 10) ((v 0) * ((v 11) ^ 2))
    rw [show (v 10) * ((v 0) * ((v 11) ^ 2)) = ((v 0) * (v 10) * ((v 11) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix h10]
  rw [(c_9_1 m ((v 0) * (v 10) * ((v 11) ^ 2)) (v 11)).left_comm]
  rw [(c_9_14 m ((v 0) * (v 10) * ((v 11) ^ 2)) ((v 0) * (v 11))).left_comm]
  rw [(c_9_3 m ((v 0) * (v 10) * ((v 11) ^ 2)) ((v 10) * ((v 11) ^ 2))).left_comm]
  rw [(c_14_3 m ((v 0) * (v 11)) ((v 10) * ((v 11) ^ 2))).left_comm]
  rw [add_suffix m 9 ((v 0) * (v 10) * ((v 11) ^ 2)) ((v 0) * (v 10) * ((v 11) ^ 2)),
    show ((v 0) * (v 10) * ((v 11) ^ 2)) + ((v 0) * (v 10) * ((v 11) ^ 2)) = 0 by ring_nf; simp only [CharTwo.two_eq_zero, mul_zero], xz, one_mul]

private theorem first_1 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 0) * (X m 10 ((v 0) * ((v 11) ^ 2)) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 3 ((v 10) * ((v 11) ^ 2)) * (X m 14 ((v 0) * (v 11)) * (X m 17 (v 1) * (X m 10 (v 2) * (X m 11 (v 3) * (X m 15 (v 4) * (X m 14 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (X m 9 (v 8) * (X m 8 (v 9) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 2 ((v 10) * (v 11)) * (1)))))))))))))))))) =
      X m 16 (v 0) * (X m 17 (v 1) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2))) * (X m 11 ((v 1) * (v 10)) * (X m 0 (v 10) * (X m 9 ((v 10) * (v 2)) * (X m 1 (v 11) * (X m 3 ((v 10) * ((v 11) ^ 2)) * (X m 14 ((v 0) * (v 11)) * (X m 15 ((v 10) * ((v 1) ^ 2)) * (X m 11 (v 3) * (X m 15 (v 4) * (X m 14 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (X m 9 (v 8) * (X m 8 (v 9) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 2 ((v 10) * (v 11)) * (1)))))))))))))))))))) := by
  rw [(c_14_17 m ((v 0) * (v 11)) (v 1)).left_comm]
  rw [(c_3_17 m ((v 10) * ((v 11) ^ 2)) (v 1)).left_comm]
  rw [(c_1_17 m (v 11) (v 1)).left_comm]
  have h3 : X m 0 (v 10) * X m 17 (v 1) = X m 17 (v 1) * X m 0 (v 10) * X m 11 ((v 1) * (v 10)) * X m 15 ((v 10) * ((v 1) ^ 2)) := by
    have h := s_0_17 m (v 10) (v 1)
    rw [show (v 10) * (v 1) = ((v 1) * (v 10)) by ring, show (v 10) * (v 1) ^ 2 = ((v 10) * ((v 1) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h3]
  rw [(c_10_17 m ((v 0) * ((v 11) ^ 2)) (v 1)).left_comm]
  rw [(c_0_11 m (v 10) ((v 1) * (v 10))).left_comm]
  rw [(c_15_1 m ((v 10) * ((v 1) ^ 2)) (v 11)).left_comm]
  rw [(c_15_3 m ((v 10) * ((v 1) ^ 2)) ((v 10) * ((v 11) ^ 2))).left_comm]
  rw [(c_15_14 m ((v 10) * ((v 1) ^ 2)) ((v 0) * (v 11))).left_comm]
  rw [(c_15_10 m ((v 10) * ((v 1) ^ 2)) (v 2)).left_comm]
  rw [(c_14_10 m ((v 0) * (v 11)) (v 2)).left_comm]
  rw [(c_3_10 m ((v 10) * ((v 11) ^ 2)) (v 2)).left_comm]
  rw [(c_1_10 m (v 11) (v 2)).left_comm]
  have h13 : X m 0 (v 10) * X m 10 (v 2) = X m 10 (v 2) * X m 0 (v 10) * X m 9 ((v 10) * (v 2)) := by
    have h := s_0_10 m (v 10) (v 2)
    rw [show (v 10) * (v 2) = ((v 10) * (v 2)) by ring] at h
    exact h
  rw [swap_suffix h13]
  rw [(c_11_10 m ((v 1) * (v 10)) (v 2)).left_comm]
  rw [add_suffix m 10 ((v 0) * ((v 11) ^ 2)) (v 2),
    show ((v 0) * ((v 11) ^ 2)) + (v 2) = ((v 2) + ((v 0) * ((v 11) ^ 2))) by ring]

private theorem first_2 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 0) * (X m 17 (v 1) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2))) * (X m 11 ((v 1) * (v 10)) * (X m 0 (v 10) * (X m 9 ((v 10) * (v 2)) * (X m 1 (v 11) * (X m 3 ((v 10) * ((v 11) ^ 2)) * (X m 14 ((v 0) * (v 11)) * (X m 15 ((v 10) * ((v 1) ^ 2)) * (X m 11 (v 3) * (X m 15 (v 4) * (X m 14 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (X m 9 (v 8) * (X m 8 (v 9) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 2 ((v 10) * (v 11)) * (1)))))))))))))))))))) =
      X m 16 (v 0) * (X m 17 (v 1) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2))) * (X m 11 ((v 3) + ((v 1) * (v 10))) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 3 ((v 10) * ((v 11) ^ 2)) * (X m 14 ((v 0) * (v 11)) * (X m 15 ((v 10) * ((v 1) ^ 2)) * (X m 15 (v 4) * (X m 8 ((v 11) * (v 3)) * (X m 9 ((v 10) * (v 2)) * (X m 14 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (X m 9 (v 8) * (X m 8 (v 9) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 2 ((v 10) * (v 11)) * (1)))))))))))))))))))) := by
  rw [(c_9_1 m ((v 10) * (v 2)) (v 11)).left_comm]
  rw [(c_9_3 m ((v 10) * (v 2)) ((v 10) * ((v 11) ^ 2))).left_comm]
  rw [(c_9_14 m ((v 10) * (v 2)) ((v 0) * (v 11))).left_comm]
  rw [(c_9_15 m ((v 10) * (v 2)) ((v 10) * ((v 1) ^ 2))).left_comm]
  rw [(c_9_11 m ((v 10) * (v 2)) (v 3)).left_comm]
  rw [(c_15_11 m ((v 10) * ((v 1) ^ 2)) (v 3)).left_comm]
  rw [(c_14_11 m ((v 0) * (v 11)) (v 3)).left_comm]
  rw [(c_3_11 m ((v 10) * ((v 11) ^ 2)) (v 3)).left_comm]
  have h8 : X m 1 (v 11) * X m 11 (v 3) = X m 11 (v 3) * X m 1 (v 11) * X m 8 ((v 11) * (v 3)) := by
    have h := s_1_11 m (v 11) (v 3)
    rw [show (v 11) * (v 3) = ((v 11) * (v 3)) by ring] at h
    exact h
  rw [swap_suffix h8]
  rw [(c_0_11 m (v 10) (v 3)).left_comm]
  rw [add_suffix m 11 ((v 1) * (v 10)) (v 3),
    show ((v 1) * (v 10)) + (v 3) = ((v 3) + ((v 1) * (v 10))) by ring]
  rw [(c_8_3 m ((v 11) * (v 3)) ((v 10) * ((v 11) ^ 2))).left_comm]
  rw [(c_8_14 m ((v 11) * (v 3)) ((v 0) * (v 11))).left_comm]
  rw [(c_8_15 m ((v 11) * (v 3)) ((v 10) * ((v 1) ^ 2))).left_comm]
  rw [(c_9_15 m ((v 10) * (v 2)) (v 4)).left_comm]
  rw [(c_8_15 m ((v 11) * (v 3)) (v 4)).left_comm]

private theorem first_3 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 0) * (X m 17 (v 1) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2))) * (X m 11 ((v 3) + ((v 1) * (v 10))) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 3 ((v 10) * ((v 11) ^ 2)) * (X m 14 ((v 0) * (v 11)) * (X m 15 ((v 10) * ((v 1) ^ 2)) * (X m 15 (v 4) * (X m 8 ((v 11) * (v 3)) * (X m 9 ((v 10) * (v 2)) * (X m 14 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (X m 9 (v 8) * (X m 8 (v 9) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 2 ((v 10) * (v 11)) * (1)))))))))))))))))))) =
      X m 16 (v 0) * (X m 17 (v 1) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2))) * (X m 11 ((v 3) + ((v 1) * (v 10))) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 3 ((v 10) * ((v 11) ^ 2)) * (X m 14 ((v 5) + ((v 0) * (v 11))) * (X m 15 ((v 4) + ((v 10) * ((v 1) ^ 2))) * (X m 20 (v 7) * (X m 0 (v 10) * (X m 21 (v 6) * (X m 16 ((v 10) * (v 6)) * (X m 8 ((v 9) + ((v 11) * (v 3))) * (X m 9 ((v 8) + ((v 10) * (v 2))) * (X m 1 (v 11) * (X m 2 ((v 10) * (v 11)) * (1))))))))))))))))) := by
  rw [add_suffix m 15 ((v 10) * ((v 1) ^ 2)) (v 4),
    show ((v 10) * ((v 1) ^ 2)) + (v 4) = ((v 4) + ((v 10) * ((v 1) ^ 2))) by ring]
  rw [(c_9_14 m ((v 10) * (v 2)) (v 5)).left_comm]
  rw [(c_8_14 m ((v 11) * (v 3)) (v 5)).left_comm]
  rw [(c_15_14 m ((v 4) + ((v 10) * ((v 1) ^ 2))) (v 5)).left_comm]
  rw [add_suffix m 14 ((v 0) * (v 11)) (v 5),
    show ((v 0) * (v 11)) + (v 5) = ((v 5) + ((v 0) * (v 11))) by ring]
  rw [(c_9_21 m ((v 10) * (v 2)) (v 6)).left_comm]
  rw [(c_8_21 m ((v 11) * (v 3)) (v 6)).left_comm]
  rw [(c_9_20 m ((v 10) * (v 2)) (v 7)).left_comm]
  rw [(c_8_20 m ((v 11) * (v 3)) (v 7)).left_comm]
  rw [(c_21_20 m (v 6) (v 7)).left_comm]
  rw [add_suffix m 9 ((v 10) * (v 2)) (v 8),
    show ((v 10) * (v 2)) + (v 8) = ((v 8) + ((v 10) * (v 2))) by ring]
  rw [(c_9_8 m ((v 8) + ((v 10) * (v 2))) (v 9)).left_comm]
  rw [add_suffix m 8 ((v 11) * (v 3)) (v 9),
    show ((v 11) * (v 3)) + (v 9) = ((v 9) + ((v 11) * (v 3))) by ring]
  rw [(c_9_0 m ((v 8) + ((v 10) * (v 2))) (v 10)).left_comm]
  rw [(c_8_0 m ((v 9) + ((v 11) * (v 3))) (v 10)).left_comm]
  have h15 : X m 21 (v 6) * X m 0 (v 10) = X m 0 (v 10) * X m 21 (v 6) * X m 16 ((v 10) * (v 6)) := by
    have h := s_21_0 m (v 6) (v 10)
    rw [show (v 6) * (v 10) = ((v 10) * (v 6)) by ring] at h
    exact h
  rw [swap_suffix h15]

private theorem first_4 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 0) * (X m 17 (v 1) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2))) * (X m 11 ((v 3) + ((v 1) * (v 10))) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 3 ((v 10) * ((v 11) ^ 2)) * (X m 14 ((v 5) + ((v 0) * (v 11))) * (X m 15 ((v 4) + ((v 10) * ((v 1) ^ 2))) * (X m 20 (v 7) * (X m 0 (v 10) * (X m 21 (v 6) * (X m 16 ((v 10) * (v 6)) * (X m 8 ((v 9) + ((v 11) * (v 3))) * (X m 9 ((v 8) + ((v 10) * (v 2))) * (X m 1 (v 11) * (X m 2 ((v 10) * (v 11)) * (1))))))))))))))))) =
      X m 16 (v 0) * (X m 16 ((v 10) * (v 6)) * (X m 17 (v 1) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2))) * (X m 11 ((v 3) + ((v 1) * (v 10))) * (X m 1 (v 11) * (X m 14 ((v 10) * (v 11) * (v 6)) * (X m 10 ((v 10) * (v 6) * ((v 11) ^ 2)) * (X m 2 ((v 10) * (v 11)) * (X m 14 ((v 5) + ((v 0) * (v 11))) * (X m 15 ((v 4) + ((v 10) * ((v 1) ^ 2))) * (X m 20 (v 7) * (X m 21 (v 6) * (X m 8 ((v 9) + ((v 11) * (v 3))) * (X m 9 ((v 8) + ((v 10) * (v 2))) * (X m 1 (v 11) * (X m 2 ((v 10) * (v 11)) * (1))))))))))))))))) := by
  rw [(c_20_0 m (v 7) (v 10)).left_comm]
  rw [(c_15_0 m ((v 4) + ((v 10) * ((v 1) ^ 2))) (v 10)).left_comm]
  rw [(c_14_0 m ((v 5) + ((v 0) * (v 11))) (v 10)).left_comm]
  rw [(c_3_0 m ((v 10) * ((v 11) ^ 2)) (v 10)).left_comm]
  have h4 : X m 1 (v 11) * X m 0 (v 10) = X m 0 (v 10) * X m 1 (v 11) * X m 2 ((v 10) * (v 11)) * X m 3 ((v 10) * ((v 11) ^ 2)) := by
    have h := s_1_0 m (v 11) (v 10)
    rw [show (v 11) * (v 10) = ((v 10) * (v 11)) by ring, show (v 10) * (v 11) ^ 2 = ((v 10) * ((v 11) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h4]
  rw [add_suffix m 0 (v 10) (v 10),
    show (v 10) + (v 10) = 0 by ring_nf; simp only [CharTwo.two_eq_zero, mul_zero], xz, one_mul]
  rw [add_suffix m 3 ((v 10) * ((v 11) ^ 2)) ((v 10) * ((v 11) ^ 2)),
    show ((v 10) * ((v 11) ^ 2)) + ((v 10) * ((v 11) ^ 2)) = 0 by ring_nf; simp only [CharTwo.two_eq_zero, mul_zero], xz, one_mul]
  rw [(c_21_16 m (v 6) ((v 10) * (v 6))).left_comm]
  rw [(c_20_16 m (v 7) ((v 10) * (v 6))).left_comm]
  rw [(c_15_16 m ((v 4) + ((v 10) * ((v 1) ^ 2))) ((v 10) * (v 6))).left_comm]
  rw [(c_14_16 m ((v 5) + ((v 0) * (v 11))) ((v 10) * (v 6))).left_comm]
  rw [(c_2_16 m ((v 10) * (v 11)) ((v 10) * (v 6))).left_comm]
  have h12 : X m 1 (v 11) * X m 16 ((v 10) * (v 6)) = X m 16 ((v 10) * (v 6)) * X m 1 (v 11) * X m 14 ((v 10) * (v 11) * (v 6)) * X m 10 ((v 10) * (v 6) * ((v 11) ^ 2)) := by
    have h := s_1_16 m (v 11) ((v 10) * (v 6))
    rw [show (v 11) * ((v 10) * (v 6)) = ((v 10) * (v 11) * (v 6)) by ring, show ((v 10) * (v 6)) * (v 11) ^ 2 = ((v 10) * (v 6) * ((v 11) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h12]
  rw [(c_11_16 m ((v 3) + ((v 1) * (v 10))) ((v 10) * (v 6))).left_comm]
  rw [(c_10_16 m ((v 2) + ((v 0) * ((v 11) ^ 2))) ((v 10) * (v 6))).left_comm]
  rw [(c_17_16 m (v 1) ((v 10) * (v 6))).left_comm]

private theorem first_5 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 0) * (X m 16 ((v 10) * (v 6)) * (X m 17 (v 1) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2))) * (X m 11 ((v 3) + ((v 1) * (v 10))) * (X m 1 (v 11) * (X m 14 ((v 10) * (v 11) * (v 6)) * (X m 10 ((v 10) * (v 6) * ((v 11) ^ 2)) * (X m 2 ((v 10) * (v 11)) * (X m 14 ((v 5) + ((v 0) * (v 11))) * (X m 15 ((v 4) + ((v 10) * ((v 1) ^ 2))) * (X m 20 (v 7) * (X m 21 (v 6) * (X m 8 ((v 9) + ((v 11) * (v 3))) * (X m 9 ((v 8) + ((v 10) * (v 2))) * (X m 1 (v 11) * (X m 2 ((v 10) * (v 11)) * (1))))))))))))))))) =
      X m 16 ((v 0) + ((v 10) * (v 6))) * (X m 17 (v 1) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2)) + ((v 10) * (v 6) * ((v 11) ^ 2))) * (X m 11 ((v 3) + ((v 1) * (v 10))) * (X m 2 ((v 10) * (v 11)) * (X m 14 ((v 5) + ((v 0) * (v 11)) + ((v 10) * (v 11) * (v 6))) * (X m 15 ((v 4) + ((v 10) * ((v 1) ^ 2))) * (X m 17 ((v 11) * (v 7)) * (X m 20 (v 7) * (X m 21 (v 6) * (X m 8 ((v 9) + ((v 11) * (v 3))) * (X m 9 ((v 8) + ((v 10) * (v 2))) * (X m 2 ((v 10) * (v 11)) * (1))))))))))))) := by
  rw [add_suffix m 16 (v 0) ((v 10) * (v 6)),
    show (v 0) + ((v 10) * (v 6)) = ((v 0) + ((v 10) * (v 6))) by ring]
  rw [(c_14_10 m ((v 10) * (v 11) * (v 6)) ((v 10) * (v 6) * ((v 11) ^ 2))).left_comm]
  rw [(c_1_10 m (v 11) ((v 10) * (v 6) * ((v 11) ^ 2))).left_comm]
  rw [(c_11_10 m ((v 3) + ((v 1) * (v 10))) ((v 10) * (v 6) * ((v 11) ^ 2))).left_comm]
  rw [add_suffix m 10 ((v 2) + ((v 0) * ((v 11) ^ 2))) ((v 10) * (v 6) * ((v 11) ^ 2)),
    show ((v 2) + ((v 0) * ((v 11) ^ 2))) + ((v 10) * (v 6) * ((v 11) ^ 2)) = ((v 2) + ((v 0) * ((v 11) ^ 2)) + ((v 10) * (v 6) * ((v 11) ^ 2))) by ring]
  rw [(c_14_2 m ((v 10) * (v 11) * (v 6)) ((v 10) * (v 11))).left_comm]
  rw [add_suffix m 14 ((v 10) * (v 11) * (v 6)) ((v 5) + ((v 0) * (v 11))),
    show ((v 10) * (v 11) * (v 6)) + ((v 5) + ((v 0) * (v 11))) = ((v 5) + ((v 0) * (v 11)) + ((v 10) * (v 11) * (v 6))) by ring]
  rw [(c_9_1 m ((v 8) + ((v 10) * (v 2))) (v 11)).left_comm]
  rw [(c_8_1 m ((v 9) + ((v 11) * (v 3))) (v 11)).left_comm]
  rw [(c_21_1 m (v 6) (v 11)).left_comm]
  have h10 : X m 20 (v 7) * X m 1 (v 11) = X m 1 (v 11) * X m 20 (v 7) * X m 17 ((v 11) * (v 7)) := by
    have h := s_20_1 m (v 7) (v 11)
    rw [show (v 7) * (v 11) = ((v 11) * (v 7)) by ring] at h
    exact h
  rw [swap_suffix h10]
  rw [(c_15_1 m ((v 4) + ((v 10) * ((v 1) ^ 2))) (v 11)).left_comm]
  rw [(c_14_1 m ((v 5) + ((v 0) * (v 11)) + ((v 10) * (v 11) * (v 6))) (v 11)).left_comm]
  rw [(c_2_1 m ((v 10) * (v 11)) (v 11)).left_comm]
  rw [add_suffix m 1 (v 11) (v 11),
    show (v 11) + (v 11) = 0 by ring_nf; simp only [CharTwo.two_eq_zero, mul_zero], xz, one_mul]
  rw [(c_20_17 m (v 7) ((v 11) * (v 7))).left_comm]

private theorem first_6 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 ((v 0) + ((v 10) * (v 6))) * (X m 17 (v 1) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2)) + ((v 10) * (v 6) * ((v 11) ^ 2))) * (X m 11 ((v 3) + ((v 1) * (v 10))) * (X m 2 ((v 10) * (v 11)) * (X m 14 ((v 5) + ((v 0) * (v 11)) + ((v 10) * (v 11) * (v 6))) * (X m 15 ((v 4) + ((v 10) * ((v 1) ^ 2))) * (X m 17 ((v 11) * (v 7)) * (X m 20 (v 7) * (X m 21 (v 6) * (X m 8 ((v 9) + ((v 11) * (v 3))) * (X m 9 ((v 8) + ((v 10) * (v 2))) * (X m 2 ((v 10) * (v 11)) * (1))))))))))))) =
      X m 16 ((v 0) + ((v 10) * (v 6))) * (X m 17 ((v 1) + ((v 11) * (v 7))) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2)) + ((v 10) * (v 6) * ((v 11) ^ 2))) * (X m 11 ((v 3) + ((v 1) * (v 10))) * (X m 2 ((v 10) * (v 11)) * (X m 14 ((v 5) + ((v 0) * (v 11)) + ((v 10) * (v 11) * (v 6))) * (X m 2 ((v 10) * (v 11)) * (X m 15 ((v 4) + ((v 10) * ((v 1) ^ 2))) * (X m 20 (v 7) * (X m 11 ((v 10) * (v 11) * (v 7)) * (X m 21 (v 6) * (X m 14 ((v 10) * (v 11) * (v 6)) * (X m 9 ((v 6) * ((v 10) ^ 2) * ((v 11) ^ 2)) * (X m 8 ((v 9) + ((v 11) * (v 3)) + ((v 10) * (v 7) * ((v 11) ^ 2))) * (X m 9 ((v 8) + ((v 10) * (v 2))) * (1))))))))))))))) := by
  rw [(c_15_17 m ((v 4) + ((v 10) * ((v 1) ^ 2))) ((v 11) * (v 7))).left_comm]
  rw [(c_14_17 m ((v 5) + ((v 0) * (v 11)) + ((v 10) * (v 11) * (v 6))) ((v 11) * (v 7))).left_comm]
  have h2 : X m 2 ((v 10) * (v 11)) * X m 17 ((v 11) * (v 7)) = X m 17 ((v 11) * (v 7)) * X m 2 ((v 10) * (v 11)) * X m 8 ((v 10) * (v 7) * ((v 11) ^ 2)) := by
    have h := s_2_17 m ((v 10) * (v 11)) ((v 11) * (v 7))
    rw [show ((v 10) * (v 11)) * ((v 11) * (v 7)) = ((v 10) * (v 7) * ((v 11) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix h2]
  rw [(c_11_17 m ((v 3) + ((v 1) * (v 10))) ((v 11) * (v 7))).left_comm]
  rw [(c_10_17 m ((v 2) + ((v 0) * ((v 11) ^ 2)) + ((v 10) * (v 6) * ((v 11) ^ 2))) ((v 11) * (v 7))).left_comm]
  rw [add_suffix m 17 (v 1) ((v 11) * (v 7)),
    show (v 1) + ((v 11) * (v 7)) = ((v 1) + ((v 11) * (v 7))) by ring]
  rw [(c_8_14 m ((v 10) * (v 7) * ((v 11) ^ 2)) ((v 5) + ((v 0) * (v 11)) + ((v 10) * (v 11) * (v 6)))).left_comm]
  rw [(c_8_15 m ((v 10) * (v 7) * ((v 11) ^ 2)) ((v 4) + ((v 10) * ((v 1) ^ 2)))).left_comm]
  rw [(c_8_20 m ((v 10) * (v 7) * ((v 11) ^ 2)) (v 7)).left_comm]
  rw [(c_8_21 m ((v 10) * (v 7) * ((v 11) ^ 2)) (v 6)).left_comm]
  rw [add_suffix m 8 ((v 10) * (v 7) * ((v 11) ^ 2)) ((v 9) + ((v 11) * (v 3))),
    show ((v 10) * (v 7) * ((v 11) ^ 2)) + ((v 9) + ((v 11) * (v 3))) = ((v 9) + ((v 11) * (v 3)) + ((v 10) * (v 7) * ((v 11) ^ 2))) by ring]
  rw [(c_9_2 m ((v 8) + ((v 10) * (v 2))) ((v 10) * (v 11))).left_comm]
  rw [(c_8_2 m ((v 9) + ((v 11) * (v 3)) + ((v 10) * (v 7) * ((v 11) ^ 2))) ((v 10) * (v 11))).left_comm]
  have h13 : X m 21 (v 6) * X m 2 ((v 10) * (v 11)) = X m 2 ((v 10) * (v 11)) * X m 21 (v 6) * X m 14 ((v 10) * (v 11) * (v 6)) * X m 9 ((v 6) * ((v 10) ^ 2) * ((v 11) ^ 2)) := by
    have h := s_21_2 m (v 6) ((v 10) * (v 11))
    rw [show (v 6) * ((v 10) * (v 11)) = ((v 10) * (v 11) * (v 6)) by ring, show (v 6) * ((v 10) * (v 11)) ^ 2 = ((v 6) * ((v 10) ^ 2) * ((v 11) ^ 2)) by ring] at h
    exact h
  rw [swap_suffix_two h13]
  have h14 : X m 20 (v 7) * X m 2 ((v 10) * (v 11)) = X m 2 ((v 10) * (v 11)) * X m 20 (v 7) * X m 11 ((v 10) * (v 11) * (v 7)) := by
    have h := s_20_2 m (v 7) ((v 10) * (v 11))
    rw [show (v 7) * ((v 10) * (v 11)) = ((v 10) * (v 11) * (v 7)) by ring] at h
    exact h
  rw [swap_suffix h14]
  rw [(c_15_2 m ((v 4) + ((v 10) * ((v 1) ^ 2))) ((v 10) * (v 11))).left_comm]

private theorem first_7 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 ((v 0) + ((v 10) * (v 6))) * (X m 17 ((v 1) + ((v 11) * (v 7))) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2)) + ((v 10) * (v 6) * ((v 11) ^ 2))) * (X m 11 ((v 3) + ((v 1) * (v 10))) * (X m 2 ((v 10) * (v 11)) * (X m 14 ((v 5) + ((v 0) * (v 11)) + ((v 10) * (v 11) * (v 6))) * (X m 2 ((v 10) * (v 11)) * (X m 15 ((v 4) + ((v 10) * ((v 1) ^ 2))) * (X m 20 (v 7) * (X m 11 ((v 10) * (v 11) * (v 7)) * (X m 21 (v 6) * (X m 14 ((v 10) * (v 11) * (v 6)) * (X m 9 ((v 6) * ((v 10) ^ 2) * ((v 11) ^ 2)) * (X m 8 ((v 9) + ((v 11) * (v 3)) + ((v 10) * (v 7) * ((v 11) ^ 2))) * (X m 9 ((v 8) + ((v 10) * (v 2))) * (1))))))))))))))) =
      X m 16 ((v 0) + ((v 10) * (v 6))) * (X m 17 ((v 1) + ((v 11) * (v 7))) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2)) + ((v 10) * (v 6) * ((v 11) ^ 2))) * (X m 11 ((v 3) + ((v 1) * (v 10)) + ((v 10) * (v 11) * (v 7))) * (X m 14 ((v 5) + ((v 0) * (v 11))) * (X m 15 ((v 4) + ((v 10) * ((v 1) ^ 2))) * (X m 20 (v 7) * (X m 21 (v 6) * (X m 8 ((v 9) + ((v 11) * (v 3)) + ((v 10) * (v 7) * ((v 11) ^ 2))) * (X m 9 ((v 8) + ((v 10) * (v 2)) + ((v 6) * ((v 10) ^ 2) * ((v 11) ^ 2))) * (1)))))))))) := by
  rw [(c_14_2 m ((v 5) + ((v 0) * (v 11)) + ((v 10) * (v 11) * (v 6))) ((v 10) * (v 11))).left_comm]
  rw [add_suffix m 2 ((v 10) * (v 11)) ((v 10) * (v 11)),
    show ((v 10) * (v 11)) + ((v 10) * (v 11)) = 0 by ring_nf; simp only [CharTwo.two_eq_zero, mul_zero], xz, one_mul]
  rw [(c_20_11 m (v 7) ((v 10) * (v 11) * (v 7))).left_comm]
  rw [(c_15_11 m ((v 4) + ((v 10) * ((v 1) ^ 2))) ((v 10) * (v 11) * (v 7))).left_comm]
  rw [(c_14_11 m ((v 5) + ((v 0) * (v 11)) + ((v 10) * (v 11) * (v 6))) ((v 10) * (v 11) * (v 7))).left_comm]
  rw [add_suffix m 11 ((v 3) + ((v 1) * (v 10))) ((v 10) * (v 11) * (v 7)),
    show ((v 3) + ((v 1) * (v 10))) + ((v 10) * (v 11) * (v 7)) = ((v 3) + ((v 1) * (v 10)) + ((v 10) * (v 11) * (v 7))) by ring]
  rw [(c_21_14 m (v 6) ((v 10) * (v 11) * (v 6))).left_comm]
  rw [(c_20_14 m (v 7) ((v 10) * (v 11) * (v 6))).left_comm]
  rw [(c_15_14 m ((v 4) + ((v 10) * ((v 1) ^ 2))) ((v 10) * (v 11) * (v 6))).left_comm]
  rw [add_suffix m 14 ((v 5) + ((v 0) * (v 11)) + ((v 10) * (v 11) * (v 6))) ((v 10) * (v 11) * (v 6)),
    show ((v 5) + ((v 0) * (v 11)) + ((v 10) * (v 11) * (v 6))) + ((v 10) * (v 11) * (v 6)) = ((v 5) + ((v 0) * (v 11))) by ring_nf; simp only [CharTwo.two_eq_zero, mul_zero, add_zero]]
  rw [(c_9_8 m ((v 6) * ((v 10) ^ 2) * ((v 11) ^ 2)) ((v 9) + ((v 11) * (v 3)) + ((v 10) * (v 7) * ((v 11) ^ 2)))).left_comm]
  rw [add_suffix m 9 ((v 6) * ((v 10) ^ 2) * ((v 11) ^ 2)) ((v 8) + ((v 10) * (v 2))),
    show ((v 6) * ((v 10) ^ 2) * ((v 11) ^ 2)) + ((v 8) + ((v 10) * (v 2))) = ((v 8) + ((v 10) * (v 2)) + ((v 6) * ((v 10) ^ 2) * ((v 11) ^ 2))) by ring]

theorem collect_first_tail (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 2 ((v 10) * (v 11)) * (X m 1 (v 11) * (X m 0 (v 10) * (X m 16 (v 0) * (X m 17 (v 1) * (X m 10 (v 2) * (X m 11 (v 3) * (X m 15 (v 4) * (X m 14 (v 5) * (X m 21 (v 6) * (X m 20 (v 7) * (X m 9 (v 8) * (X m 8 (v 9) * (X m 0 (v 10) * (X m 1 (v 11) * (X m 2 ((v 10) * (v 11)) * (1)))))))))))))))) =
      X m 16 ((v 0) + ((v 10) * (v 6))) * (X m 17 ((v 1) + ((v 11) * (v 7))) * (X m 10 ((v 2) + ((v 0) * ((v 11) ^ 2)) + ((v 10) * (v 6) * ((v 11) ^ 2))) * (X m 11 ((v 3) + ((v 1) * (v 10)) + ((v 10) * (v 11) * (v 7))) * (X m 14 ((v 5) + ((v 0) * (v 11))) * (X m 15 ((v 4) + ((v 10) * ((v 1) ^ 2))) * (X m 20 (v 7) * (X m 21 (v 6) * (X m 8 ((v 9) + ((v 11) * (v 3)) + ((v 10) * (v 7) * ((v 11) ^ 2))) * (X m 9 ((v 8) + ((v 10) * (v 2)) + ((v 6) * ((v 10) ^ 2) * ((v 11) ^ 2))) * (1)))))))))) := by
  exact (first_0 m v).trans ((first_1 m v).trans ((first_2 m v).trans ((first_3 m v).trans ((first_4 m v).trans ((first_5 m v).trans ((first_6 m v).trans ((first_7 m v))))))))

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.TailCompression
