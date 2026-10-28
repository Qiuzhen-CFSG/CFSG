module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords
public import Mathlib.Tactic.Abel

/-!
# First-block split-root conjugation

Conjugation by one split root preserves the absent first B₂ block. The
collected coordinates at roots 22, 18 and 6 give exactly the relative
coordinates needed to normalize X₇ and X₃. The consumer composes four such
identities and then recovers the actual Ree coordinates by uniqueness.
Each exchange and scalar identity is checked in Lean. The generator in
`source/generate.py` is only a proof-writing tool.

Source: GLS3 Table 2.4 and 2.4.5(d), refs/KGroup/GLS3/chapter2.tex.
-/

public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.MainNormalizationCalculation
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent.OuterElimination
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local irreducible] X
private theorem c_0_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 0 a) (X m 4 b) :=
  xc m 0 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_0_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 0 a) (X m 5 b) :=
  xc m 0 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem s_0_22 (m : ℕ) (a b : CoefficientField m) :
    X m 0 a * X m 22 b = X m 22 b * X m 0 a * X m 18 (a*b) :=
  xs m 0 22 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_0_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 0 a) (X m 23 b) :=
  xc m 0 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_5_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 5 a) (X m 4 b) :=
  xc m 5 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_6_0 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 0 b = X m 0 b * X m 6 a * X m 4 (a*b) :=
  xs m 6 0 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_6_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 4 b) :=
  xc m 6 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 0 b) :=
  xc m 7 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 4 b) :=
  xc m 7 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_7_6 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 6 b = X m 6 b * X m 7 a * X m 8 (a*b) * X m 9 (b*a^2) := by
  simpa only [mul_comm] using xb m 6 7 8 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_7_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 12 b) :=
  xc m 7 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 16 b) :=
  xc m 7 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 20 b) :=
  xc m 7 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 21 b) :=
  xc m 7 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 0 b) :=
  xc m 8 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 4 b) :=
  xc m 8 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 6 b) :=
  xc m 8 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_7 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 7 b) :=
  xc m 8 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_9_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 0 b) :=
  xc m 9 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 4 b) :=
  xc m 9 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_10_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 16 b) :=
  xc m 10 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 4 b) :=
  xc m 11 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 10 b) :=
  xc m 11 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 16 b) :=
  xc m 11 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 17 b) :=
  xc m 11 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 0 b) :=
  xc m 12 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_12_4 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 4 b = X m 4 b * X m 12 a * X m 9 (a*b) :=
  xs m 12 4 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_12_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 10 b) :=
  xc m 12 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 16 b) :=
  xc m 12 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 0 b) :=
  xc m 13 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 4 b) :=
  xc m 13 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 10 b) :=
  xc m 13 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_13_12 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 12 b = X m 12 b * X m 13 a * X m 14 (a*b) * X m 15 (b*a^2) := by
  simpa only [mul_comm] using xb m 12 13 14 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_13_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 16 b) :=
  xc m 13 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 0 b) :=
  xc m 14 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 4 b) :=
  xc m 14 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 10 b) :=
  xc m 14 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 12 b) :=
  xc m 14 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 16 b) :=
  xc m 14 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 0 b) :=
  xc m 15 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 4 b) :=
  xc m 15 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_16_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 16 a) (X m 4 b) :=
  xc m 16 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 4 b) :=
  xc m 17 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 16 b) :=
  xc m 17 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_18_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 0 b) :=
  xc m 18 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_18_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 23 b) :=
  xc m 18 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_19_0 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 0 b = X m 0 b * X m 19 a * X m 7 (a*b) * X m 12 (b*a^2) := by
  simpa only [mul_comm] using xb m 0 19 7 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem s_19_4 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 4 b = X m 4 b * X m 19 a * X m 8 (a*b) * X m 10 (b*a^2) := by
  simpa only [mul_comm] using xb m 4 19 8 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_19_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 10 b) :=
  xc m 19 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 12 b) :=
  xc m 19 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 15 b) :=
  xc m 19 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 16 b) :=
  xc m 19 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 0 b) :=
  xc m 20 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 4 b) :=
  xc m 20 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 15 b) :=
  xc m 20 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_20_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 16 b) :=
  xc m 20 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_21_0 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 0 b = X m 0 b * X m 21 a * X m 16 (a*b) :=
  xs m 21 0 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_21_4 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 4 b = X m 4 b * X m 21 a * X m 15 (a*b) :=
  xs m 21 4 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_21_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 15 b) :=
  xc m 21 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 16 b) :=
  xc m 21 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem chunk_0 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 0 t * (X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1)))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 0 t * (X m 11 (t * (v 22) * (v 5)) * (X m 18 (t * (v 22)) * (X m 9 (t * (v 22) * ((v 5) ^ 2)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1))))))))))))))))))))))))) := by
  have h0 : X m 0 t * X m 22 (v 22) = X m 22 (v 22) * X m 0 t * X m 18 (t * (v 22)) := by
    have h := s_0_22 m t (v 22)
    rw [show t * (v 22) = (t * (v 22)) by ring] at h
    exact h
  conv_lhs =>
    rw [swap_suffix h0]
  conv_lhs =>
    enter [2, 2]
    rw [(c_18_23 m (t * (v 22)) (v 23)).left_comm]
  conv_lhs =>
    enter [2]
    rw [(c_0_23 m t (v 23)).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_18_4 m (t * (v 22)) (v 4)).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [(c_0_4 m t (v 4)).left_comm]
  have h5 : X m 18 (t * (v 22)) * X m 5 (v 5) = X m 5 (v 5) * X m 18 (t * (v 22)) * X m 11 (t * (v 22) * (v 5)) * X m 9 (t * (v 22) * ((v 5) ^ 2)) := by
    have h := s_18_5 m (t * (v 22)) (v 5)
    rw [show (t * (v 22)) * (v 5) = (t * (v 22) * (v 5)) by ring, show (t * (v 22)) * (v 5) ^ 2 = (t * (v 22) * ((v 5) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [swap_suffix_two h5]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_0_5 m t (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_18_11 m (t * (v 22)) (t * (v 22) * (v 5))).left_comm]

private theorem chunk_1 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 0 t * (X m 11 (t * (v 22) * (v 5)) * (X m 18 (t * (v 22)) * (X m 9 (t * (v 22) * ((v 5) ^ 2)) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 11 (t * (v 22) * (v 5)) * (X m 17 (v 17) * (X m 0 t * (X m 11 (t * (v 17)) * (X m 15 (t * ((v 17) ^ 2)) * (X m 18 (t * (v 22)) * (X m 9 (t * (v 22) * ((v 5) ^ 2)) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_0_11 m t (t * (v 22) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_16 m (t * (v 22) * ((v 5) ^ 2)) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_18_16 m (t * (v 22)) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_0_16 m t (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_11_16 m (t * (v 22) * (v 5)) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_17 m (t * (v 22) * ((v 5) ^ 2)) (v 17)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_17 m (t * (v 22)) (v 17)).left_comm]
  have h7 : X m 0 t * X m 17 (v 17) = X m 17 (v 17) * X m 0 t * X m 11 (t * (v 17)) * X m 15 (t * ((v 17) ^ 2)) := by
    have h := s_0_17 m t (v 17)
    rw [show t * (v 17) = (t * (v 17)) by ring, show t * (v 17) ^ 2 = (t * ((v 17) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h7]

private theorem chunk_2 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 11 (t * (v 22) * (v 5)) * (X m 17 (v 17) * (X m 0 t * (X m 11 (t * (v 17)) * (X m 15 (t * ((v 17) ^ 2)) * (X m 18 (t * (v 22)) * (X m 9 (t * (v 22) * ((v 5) ^ 2)) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1))))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 9 (t * (v 10)) * (X m 15 (t * ((v 17) ^ 2)) * (X m 18 (t * (v 22)) * (X m 15 (t * (v 10) * (v 22)) * (X m 9 (t * (v 22) * ((v 5) ^ 2)) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1)))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_11_17 m (t * (v 22) * (v 5)) (v 17)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_0_11 m t (t * (v 17))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [add_suffix m 11 (t * (v 22) * (v 5)) (t * (v 17)),
      show (t * (v 22) * (v 5)) + (t * (v 17)) = ((t * (v 17)) + (t * (v 22) * (v 5))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_10 m (t * (v 22) * ((v 5) ^ 2)) (v 10)).left_comm]
  have h4 : X m 18 (t * (v 22)) * X m 10 (v 10) = X m 10 (v 10) * X m 18 (t * (v 22)) * X m 15 (t * (v 10) * (v 22)) := by
    have h := s_18_10 m (t * (v 22)) (v 10)
    rw [show (t * (v 22)) * (v 10) = (t * (v 10) * (v 22)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_10 m (t * ((v 17) ^ 2)) (v 10)).left_comm]
  have h6 : X m 0 t * X m 10 (v 10) = X m 10 (v 10) * X m 0 t * X m 9 (t * (v 10)) := by
    have h := s_0_10 m t (v 10)
    rw [show t * (v 10) = (t * (v 10)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h6]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_11_10 m ((t * (v 17)) + (t * (v 22) * (v 5))) (v 10)).left_comm]

private theorem chunk_3 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 9 (t * (v 10)) * (X m 15 (t * ((v 17) ^ 2)) * (X m 18 (t * (v 22)) * (X m 15 (t * (v 10) * (v 22)) * (X m 9 (t * (v 22) * ((v 5) ^ 2)) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1)))))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 15 ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 11 (v 11) * (X m 18 (t * (v 22)) * (X m 9 ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1)))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m (t * (v 10)) (t * ((v 17) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m (t * (v 10)) (t * (v 22))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m (t * (v 10)) (t * (v 10) * (v 22))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m (t * (v 22)) (t * (v 10) * (v 22))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 (t * ((v 17) ^ 2)) (t * (v 10) * (v 22)),
      show (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) = ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 (t * (v 10)) (t * (v 22) * ((v 5) ^ 2)),
      show (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2)) = ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_11 m ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 11)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_11 m (t * (v 22)) (v 11)).left_comm]

private theorem chunk_4 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 15 ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 11 (v 11) * (X m 18 (t * (v 22)) * (X m 9 ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1)))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 12 (v 12) * (X m 16 (t * (v 12) * (v 22)) * (X m 15 ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 18 (t * (v 22)) * (X m 9 ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1)))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_11 m ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) (v 11)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_0_11 m t (v 11)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 11 ((t * (v 17)) + (t * (v 22) * (v 5))) (v 11),
      show ((t * (v 17)) + (t * (v 22) * (v 5))) + (v 11) = ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_12 m ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 12)).left_comm]
  have h4 : X m 18 (t * (v 22)) * X m 12 (v 12) = X m 12 (v 12) * X m 18 (t * (v 22)) * X m 16 (t * (v 12) * (v 22)) := by
    have h := s_18_12 m (t * (v 22)) (v 12)
    rw [show (t * (v 22)) * (v 12) = (t * (v 12) * (v 22)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_12 m ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) (v 12)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_16 m (t * (v 22)) (t * (v 12) * (v 22))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_16 m ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) (t * (v 12) * (v 22))).left_comm]

private theorem chunk_5 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 12 (v 12) * (X m 16 (t * (v 12) * (v 22)) * (X m 15 ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 18 (t * (v 22)) * (X m 9 ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1)))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 12 (v 12) * (X m 15 ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 13 (v 13) * (X m 18 (t * (v 22)) * (X m 9 ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_16 m (v 12) (t * (v 12) * (v 22))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_0_16 m t (t * (v 12) * (v 22))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_11_16 m ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) (t * (v 12) * (v 22))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_10_16 m (v 10) (t * (v 12) * (v 22))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_17_16 m (v 17) (t * (v 12) * (v 22))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [add_suffix m 16 (v 16) (t * (v 12) * (v 22)),
      show (v 16) + (t * (v 12) * (v 22)) = ((v 16) + (t * (v 12) * (v 22))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_13 m (t * (v 22)) (v 13)).left_comm]

private theorem chunk_6 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 12 (v 12) * (X m 15 ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 13 (v 13) * (X m 18 (t * (v 22)) * (X m 9 ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 18 (t * (v 22)) * (X m 18 (v 18) * (X m 9 ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1)))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_13 m ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_14 m (t * (v 22)) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 15)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m (t * (v 22)) (v 15)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) (v 15),
      show ((t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) + (v 15) = ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 18)).left_comm]

private theorem chunk_7 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 18 (t * (v 22)) * (X m 18 (v 18) * (X m 9 ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1)))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (X m 0 t * (1)))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 18 (t * (v 22)) (v 18),
      show (t * (v 22)) + (v 18) = ((v 18) + (t * (v 22))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 8)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) (v 9),
      show ((t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) + (v 9) = ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) by abel]

private theorem chunk_8 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (X m 0 t * (1)))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 0 t * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 7 (t * (v 19)) * (X m 12 (t * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 (t * (v 21)) * (X m 6 (v 6) * (X m 4 (t * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_0 m ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) t).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_0 m (v 8) t).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_0 m (v 7) t).left_comm]
  have h3 : X m 6 (v 6) * X m 0 t = X m 0 t * X m 6 (v 6) * X m 4 (t * (v 6)) := by
    have h := s_6_0 m (v 6) t
    rw [show (v 6) * t = (t * (v 6)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h3]
  have h4 : X m 21 (v 21) * X m 0 t = X m 0 t * X m 21 (v 21) * X m 16 (t * (v 21)) := by
    have h := s_21_0 m (v 21) t
    rw [show (v 21) * t = (t * (v 21)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_0 m (v 20) t).left_comm]
  have h6 : X m 19 (v 19) * X m 0 t = X m 0 t * X m 19 (v 19) * X m 7 (t * (v 19)) * X m 12 (t * ((v 19) ^ 2)) := by
    have h := s_19_0 m (v 19) t
    rw [show (v 19) * t = (t * (v 19)) by ring, show t * (v 19) ^ 2 = (t * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h6]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_0 m ((v 18) + (t * (v 22))) t).left_comm]

private theorem chunk_9 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 0 t * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 0 t * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 7 (t * (v 19)) * (X m 12 (t * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 (t * (v 21)) * (X m 6 (v 6) * (X m 4 (t * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 12 (t * ((v 19) ^ 2)) * (X m 18 ((v 18) + (t * (v 22))) * (X m 16 ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 7 (t * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 (t * (v 21)) * (X m 6 (v 6) * (X m 4 (t * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_0 m ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) t).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_0 m (v 14) t).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_0 m (v 13) t).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_0 m (v 12) t).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 0 t t,
      show t + t = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_12 m (t * (v 19)) (t * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_12 m (v 19) (t * ((v 19) ^ 2))).left_comm]
  have h7 : X m 18 ((v 18) + (t * (v 22))) * X m 12 (t * ((v 19) ^ 2)) = X m 12 (t * ((v 19) ^ 2)) * X m 18 ((v 18) + (t * (v 22))) * X m 16 ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) := by
    have h := s_18_12 m ((v 18) + (t * (v 22))) (t * ((v 19) ^ 2))
    rw [show ((v 18) + (t * (v 22))) * (t * ((v 19) ^ 2)) = ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h7]

private theorem chunk_10 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) * (X m 12 (t * ((v 19) ^ 2)) * (X m 18 ((v 18) + (t * (v 22))) * (X m 16 ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 7 (t * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 (t * (v 21)) * (X m 6 (v 6) * (X m 4 (t * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 16 ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 7 (t * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 (t * (v 21)) * (X m 6 (v 6) * (X m 4 (t * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_12 m ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) (t * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_12 m (v 14) (t * ((v 19) ^ 2))).left_comm]
  have h2 : X m 13 (v 13) * X m 12 (t * ((v 19) ^ 2)) = X m 12 (t * ((v 19) ^ 2)) * X m 13 (v 13) * X m 14 (t * (v 13) * ((v 19) ^ 2)) * X m 15 (t * ((v 13) ^ 2) * ((v 19) ^ 2)) := by
    have h := s_13_12 m (v 13) (t * ((v 19) ^ 2))
    rw [show (v 13) * (t * ((v 19) ^ 2)) = (t * (v 13) * ((v 19) ^ 2)) by ring, show (t * ((v 19) ^ 2)) * (v 13) ^ 2 = (t * ((v 13) ^ 2) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h2]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 12 (v 12) (t * ((v 19) ^ 2)),
      show (v 12) + (t * ((v 19) ^ 2)) = ((v 12) + (t * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m (t * ((v 13) ^ 2) * ((v 19) ^ 2)) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 (t * (v 13) * ((v 19) ^ 2)) (v 14),
      show (t * (v 13) * ((v 19) ^ 2)) + (v 14) = ((v 14) + (t * (v 13) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 (t * ((v 13) ^ 2) * ((v 19) ^ 2)) ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))),
      show (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22))) = ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_16 m ((v 18) + (t * (v 22))) ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2)))).left_comm]

private theorem chunk_11 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 16 ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 7 (t * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 (t * (v 21)) * (X m 6 (v 6) * (X m 4 (t * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 7 (t * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 (t * (v 21)) * (X m 6 (v 6) * (X m 4 (t * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_16 m ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_16 m ((v 14) + (t * (v 13) * ((v 19) ^ 2))) ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_16 m (v 13) ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_16 m ((v 12) + (t * ((v 19) ^ 2))) ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_11_16 m ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_10_16 m (v 10) ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_17_16 m (v 17) ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [add_suffix m 16 ((v 16) + (t * (v 12) * (v 22))) ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))),
      show ((v 16) + (t * (v 12) * (v 22))) + ((t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) = ((v 16) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) by abel]

private theorem chunk_12 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 7 (t * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 (t * (v 21)) * (X m 6 (v 6) * (X m 4 (t * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 16 (t * (v 21)) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 7 (t * (v 19)) * (X m 6 (v 6) * (X m 4 (t * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_20 m (t * (v 19)) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_21 m (t * (v 19)) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_16 m (t * (v 19)) (t * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_16 m (v 21) (t * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_16 m (v 20) (t * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_16 m (v 19) (t * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_16 m ((v 18) + (t * (v 22))) (t * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_16 m ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) (t * (v 21))).left_comm]

private theorem chunk_13 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 16 (t * (v 21)) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 7 (t * (v 19)) * (X m 6 (v 6) * (X m 4 (t * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 4 (t * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_16 m ((v 14) + (t * (v 13) * ((v 19) ^ 2))) (t * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_16 m (v 13) (t * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_16 m ((v 12) + (t * ((v 19) ^ 2))) (t * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_11_16 m ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) (t * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_10_16 m (v 10) (t * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_17_16 m (v 17) (t * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [add_suffix m 16 ((v 16) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) (t * (v 21)),
      show ((v 16) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) + (t * (v 21)) = ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) by abel]
  have h7 : X m 7 (t * (v 19)) * X m 6 (v 6) = X m 6 (v 6) * X m 7 (t * (v 19)) * X m 8 (t * (v 19) * (v 6)) * X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) := by
    have h := s_7_6 m (t * (v 19)) (v 6)
    rw [show (t * (v 19)) * (v 6) = (t * (v 19) * (v 6)) by ring, show (v 6) * (t * (v 19)) ^ 2 = ((v 6) * (t ^ 2) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h7]

private theorem chunk_14 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 4 (t * (v 6)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 4 (t * (v 6)) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 8 (t * (v 19) * (v 6)) * (X m 10 (t * (v 6) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 (t * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_4 m ((v 6) * (t ^ 2) * ((v 19) ^ 2)) (t * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_4 m (t * (v 19) * (v 6)) (t * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_4 m (t * (v 19)) (t * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_4 m (v 6) (t * (v 6))).left_comm]
  have h4 : X m 21 (v 21) * X m 4 (t * (v 6)) = X m 4 (t * (v 6)) * X m 21 (v 21) * X m 15 (t * (v 21) * (v 6)) := by
    have h := s_21_4 m (v 21) (t * (v 6))
    rw [show (v 21) * (t * (v 6)) = (t * (v 21) * (v 6)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_4 m (v 20) (t * (v 6))).left_comm]
  have h6 : X m 19 (v 19) * X m 4 (t * (v 6)) = X m 4 (t * (v 6)) * X m 19 (v 19) * X m 8 (t * (v 19) * (v 6)) * X m 10 (t * (v 6) * ((v 19) ^ 2)) := by
    have h := s_19_4 m (v 19) (t * (v 6))
    rw [show (v 19) * (t * (v 6)) = (t * (v 19) * (v 6)) by ring, show (t * (v 6)) * (v 19) ^ 2 = (t * (v 6) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h6]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_4 m ((v 18) + (t * (v 22))) (t * (v 6))).left_comm]

private theorem chunk_15 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 4 (t * (v 6)) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 8 (t * (v 19) * (v 6)) * (X m 10 (t * (v 6) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 (t * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 4 (t * (v 6)) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 9 ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 8 (t * (v 19) * (v 6)) * (X m 10 (t * (v 6) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 (t * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_4 m ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) (t * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_4 m ((v 14) + (t * (v 13) * ((v 19) ^ 2))) (t * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_4 m (v 13) (t * (v 6))).left_comm]
  have h3 : X m 12 ((v 12) + (t * ((v 19) ^ 2))) * X m 4 (t * (v 6)) = X m 4 (t * (v 6)) * X m 12 ((v 12) + (t * ((v 19) ^ 2))) * X m 9 ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) := by
    have h := s_12_4 m ((v 12) + (t * ((v 19) ^ 2))) (t * (v 6))
    rw [show ((v 12) + (t * ((v 19) ^ 2))) * (t * (v 6)) = ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h3]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_11_4 m ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) (t * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_10_4 m (v 10) (t * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_17_4 m (v 17) (t * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_16_4 m ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) (t * (v 6))).left_comm]

private theorem chunk_16 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 4 (t * (v 6)) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 9 ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 8 (t * (v 19) * (v 6)) * (X m 10 (t * (v 6) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 (t * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 ((v 4) + (t * (v 6))) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 10 (t * (v 6) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 (t * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_5_4 m (v 5) (t * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [add_suffix m 4 (v 4) (t * (v 6)),
      show (v 4) + (t * (v 6)) = ((v 4) + (t * (v 6))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) ((v 14) + (t * (v 13) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) ((v 18) + (t * (v 22)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) (t * (v 19) * (v 6))).left_comm]

private theorem chunk_17 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 ((v 4) + (t * (v 6))) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 10 (t * (v 6) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 (t * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 ((v 4) + (t * (v 6))) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 10 (t * (v 6) * ((v 19) ^ 2)) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 15 ((t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 (t * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_10 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) (t * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_10 m (t * (v 19) * (v 6)) (t * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_10 m (v 19) (t * (v 6) * ((v 19) ^ 2))).left_comm]
  have h3 : X m 18 ((v 18) + (t * (v 22))) * X m 10 (t * (v 6) * ((v 19) ^ 2)) = X m 10 (t * (v 6) * ((v 19) ^ 2)) * X m 18 ((v 18) + (t * (v 22))) * X m 15 ((t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) := by
    have h := s_18_10 m ((v 18) + (t * (v 22))) (t * (v 6) * ((v 19) ^ 2))
    rw [show ((v 18) + (t * (v 22))) * (t * (v 6) * ((v 19) ^ 2)) = ((t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h3]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_10 m ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) (t * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_10 m ((v 14) + (t * (v 13) * ((v 19) ^ 2))) (t * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_10 m (v 13) (t * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_10 m ((v 12) + (t * ((v 19) ^ 2))) (t * (v 6) * ((v 19) ^ 2))).left_comm]

private theorem chunk_18 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 ((v 4) + (t * (v 6))) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 10 (t * (v 6) * ((v 19) ^ 2)) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 15 ((t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 (t * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 ((v 4) + (t * (v 6))) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 ((v 10) + (t * (v 6) * ((v 19) ^ 2))) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 15 (t * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_11_10 m ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) (t * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [add_suffix m 10 (v 10) (t * (v 6) * ((v 19) ^ 2)),
      show (v 10) + (t * (v 6) * ((v 19) ^ 2)) = ((v 10) + (t * (v 6) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m ((v 18) + (t * (v 22))) ((t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) ((t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))),
      show ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2))) + ((t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) = ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_20 m (t * (v 19) * (v 6)) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_21 m (t * (v 19) * (v 6)) (v 21)).left_comm]

private theorem chunk_19 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 ((v 4) + (t * (v 6))) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 ((v 10) + (t * (v 6) * ((v 19) ^ 2))) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 15 (t * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 ((v 4) + (t * (v 6))) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 ((v 10) + (t * (v 6) * ((v 19) ^ 2))) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * (v 21) * (v 6)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (t * (v 19) * (v 6)) * (X m 6 (v 6) * (X m 9 ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) (t * (v 21) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m (t * (v 19) * (v 6)) (t * (v 21) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_15 m (v 21) (t * (v 21) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_15 m (v 20) (t * (v 21) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_15 m (v 19) (t * (v 21) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m ((v 18) + (t * (v 22))) (t * (v 21) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) (t * (v 21) * (v 6)),
      show ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) + (t * (v 21) * (v 6)) = ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * (v 21) * (v 6)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) (v 6)).left_comm]

private theorem chunk_20 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 ((v 4) + (t * (v 6))) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 ((v 10) + (t * (v 6) * ((v 19) ^ 2))) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * (v 21) * (v 6)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (t * (v 19) * (v 6)) * (X m 6 (v 6) * (X m 9 ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 7 (t * (v 19)) * (X m 8 (t * (v 19) * (v 6)) * (X m 9 ((v 6) * (t ^ 2) * ((v 19) ^ 2)) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 ((v 4) + (t * (v 6))) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 ((v 10) + (t * (v 6) * ((v 19) ^ 2))) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * (v 21) * (v 6)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 7) + (t * (v 19))) * (X m 9 (t * (v 12) * (v 6)) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m (t * (v 19) * (v 6)) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) (t * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_7 m (t * (v 19) * (v 6)) (t * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) (t * (v 19) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 (t * (v 19) * (v 6)) (t * (v 19) * (v 6)),
      show (t * (v 19) * (v 6)) + (t * (v 19) * (v 6)) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) ((v 6) * (t ^ 2) * ((v 19) ^ 2)),
      show ((t * (v 12) * (v 6)) + ((v 6) * (t ^ 2) * ((v 19) ^ 2))) + ((v 6) * (t ^ 2) * ((v 19) ^ 2)) = (t * (v 12) * (v 6)) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m (t * (v 12) * (v 6)) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 7 (t * (v 19)) (v 7),
      show (t * (v 19)) + (v 7) = ((v 7) + (t * (v 19))) by abel]

private theorem chunk_21 (m : ℕ) (v : Fin 24 → CoefficientField m) (t : CoefficientField m) :
    X m 22 (v 22) * (X m 23 (v 23) * (X m 4 ((v 4) + (t * (v 6))) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 ((v 10) + (t * (v 6) * ((v 19) ^ 2))) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * (v 21) * (v 6)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 7) + (t * (v 19))) * (X m 9 (t * (v 12) * (v 6)) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) * (1))))))))))))))))))))) =
      X m 22 (v 22) * (X m 23 (v 23) * (X m 4 ((v 4) + (t * (v 6))) * (X m 5 (v 5) * (X m 16 ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 ((v 10) + (t * (v 6) * ((v 19) ^ 2))) * (X m 11 ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))) * (X m 12 ((v 12) + (t * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + (t * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * (v 21) * (v 6)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))) * (X m 18 ((v 18) + (t * (v 22))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 7) + (t * (v 19))) * (X m 8 (v 8) * (X m 9 ((v 9) + (t * (v 10)) + (t * (v 12) * (v 6)) + (t * (v 22) * ((v 5) ^ 2))) * (1)))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (t * (v 12) * (v 6)) (v 8)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 (t * (v 12) * (v 6)) ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))),
      show (t * (v 12) * (v 6)) + ((v 9) + (t * (v 10)) + (t * (v 22) * ((v 5) ^ 2))) = ((v 9) + (t * (v 10)) + (t * (v 12) * (v 6)) + (t * (v 22) * ((v 5) ^ 2))) by abel]

private theorem collected (m : ℕ) (v : Fin 24 → CoefficientField m)
    (t : CoefficientField m) :
    X m 0 t * (X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1)))))))))))))))))))))) = splitWord m ![0, 0, 0, 0, ((v 4) + (t * (v 6))), (v 5), (v 6), ((v 7) + (t * (v 19))), (v 8), ((v 9) + (t * (v 10)) + (t * (v 12) * (v 6)) + (t * (v 22) * ((v 5) ^ 2))), ((v 10) + (t * (v 6) * ((v 19) ^ 2))), ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))), ((v 12) + (t * ((v 19) ^ 2))), (v 13), ((v 14) + (t * (v 13) * ((v 19) ^ 2))), ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * (v 21) * (v 6)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))), ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))), (v 17), ((v 18) + (t * (v 22))), (v 19), (v 20), (v 21), (v 22), (v 23)] := by
  have h := (((((chunk_0 m v t).trans (chunk_1 m v t)).trans ((chunk_2 m v t).trans ((chunk_3 m v t).trans (chunk_4 m v t)))).trans (((chunk_5 m v t).trans ((chunk_6 m v t).trans (chunk_7 m v t))).trans ((chunk_8 m v t).trans ((chunk_9 m v t).trans (chunk_10 m v t))))).trans ((((chunk_11 m v t).trans (chunk_12 m v t)).trans ((chunk_13 m v t).trans ((chunk_14 m v t).trans (chunk_15 m v t)))).trans (((chunk_16 m v t).trans ((chunk_17 m v t).trans (chunk_18 m v t))).trans ((chunk_19 m v t).trans ((chunk_20 m v t).trans (chunk_21 m v t))))))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

/-- Conjugation by split root 0, with the first B₂ block absent. -/
theorem split_conjugate_0 (m : ℕ) (v : Fin 24 → CoefficientField m)
    (t : CoefficientField m) (h0 : v 0 = 0) (h1 : v 1 = 0)
    (h2 : v 2 = 0) (h3 : v 3 = 0) :
    ∃ w : Fin 24 → CoefficientField m,
      X m 0 t * splitWord m v * X m 0 t = splitWord m w ∧
      w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0 ∧ w 22 = v 22 ∧
      w 18 = ((v 18) + (t * (v 22))) ∧
      w 6 = (v 6) := by
  refine ⟨![0, 0, 0, 0, ((v 4) + (t * (v 6))), (v 5), (v 6), ((v 7) + (t * (v 19))), (v 8), ((v 9) + (t * (v 10)) + (t * (v 12) * (v 6)) + (t * (v 22) * ((v 5) ^ 2))), ((v 10) + (t * (v 6) * ((v 19) ^ 2))), ((v 11) + (t * (v 17)) + (t * (v 22) * (v 5))), ((v 12) + (t * ((v 19) ^ 2))), (v 13), ((v 14) + (t * (v 13) * ((v 19) ^ 2))), ((v 15) + (t * ((v 17) ^ 2)) + (t * (v 10) * (v 22)) + (t * (v 21) * (v 6)) + (t * ((v 13) ^ 2) * ((v 19) ^ 2)) + (t * (v 18) * (v 6) * ((v 19) ^ 2)) + ((v 22) * (v 6) * (t ^ 2) * ((v 19) ^ 2))), ((v 16) + (t * (v 21)) + (t * (v 12) * (v 22)) + (t * (v 18) * ((v 19) ^ 2)) + ((v 22) * (t ^ 2) * ((v 19) ^ 2))), (v 17), ((v 18) + (t * (v 22))), (v 19), (v 20), (v 21), (v 22), (v 23)], ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  calc
    _ = X m 0 t * (X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 0 t * (1)))))))))))))))))))))) := by
      simp only [splitWord, h0, h1, h2, h3, xz, one_mul, mul_assoc, mul_one]
    _ = _ := collected m v t

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.MainNormalizationCalculation
