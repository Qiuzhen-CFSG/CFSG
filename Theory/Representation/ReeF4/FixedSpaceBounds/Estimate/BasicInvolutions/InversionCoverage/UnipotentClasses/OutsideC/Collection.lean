module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords
public import Mathlib.Tactic.Abel

/-!
# An explicit unipotent conjugator for the nonzero eighth-coordinate branch

This calculation collects g x₈(a) g⁻¹ for
g = x₂(s) x₃(t) y₃(u) x₅(v), with independent split-root parameters.
Its consumer supplies the actual Ree parameters and solves the four resulting
coordinate equations. Every exchange uses the proved F₄ matrix relations.
The adjacent source/generate.py is an untrusted proof-writing tool.

Source: GLS3 Table 2.4 and 2.4.5(d), refs/KGroup/GLS3/chapter2.tex;
the involution-class input to Guralnick--Malle Lemma 8.8, internal p.57.
-/

public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.Collection
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent.OuterElimination
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local irreducible] X
private theorem c_4_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 4 a) (X m 22 b) :=
  xc m 4 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_4_23 (m : ℕ) (a b : CoefficientField m) :
    X m 4 a * X m 23 b = X m 23 b * X m 4 a * X m 11 (a*b) * X m 16 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 4 23 11 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 11 (a*b)) (xx m 16 (a*b^2))
    (xc m 11 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem s_5_22 (m : ℕ) (a b : CoefficientField m) :
    X m 5 a * X m 22 b = X m 22 b * X m 5 a * X m 17 (a*b) * X m 10 (b*a^2) := by
  simpa only [mul_comm] using xb m 22 5 17 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_5_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 5 a) (X m 23 b) :=
  xc m 5 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_6_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 22 b) :=
  xc m 6 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_6_23 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 23 b = X m 23 b * X m 6 a * X m 17 (a*b) * X m 21 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 6 23 17 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 17 (a*b)) (xx m 21 (a*b^2))
    (xc m 17 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

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

private theorem c_7_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 20 b) :=
  xc m 7 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_7_22 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 22 b = X m 22 b * X m 7 a * X m 20 (a*b) * X m 16 (b*a^2) := by
  simpa only [mul_comm] using xb m 22 7 20 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_7_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 23 b) :=
  xc m 7 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_8_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 22 b) :=
  xc m 8 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_8_23 (m : ℕ) (a b : CoefficientField m) :
    X m 8 a * X m 23 b = X m 23 b * X m 8 a * X m 14 (a*b) :=
  xs m 8 23 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

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

private theorem c_13_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 11 b) :=
  xc m 13 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_14_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 22 b) :=
  xc m 14 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 23 b) :=
  xc m 14 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_15_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 17 b) :=
  xc m 15 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 23 b) :=
  xc m 15 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_16_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 16 a) (X m 4 b) :=
  xc m 16 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_16_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 16 a) (X m 5 b) :=
  xc m 16 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_17_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 23 b) :=
  xc m 17 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_20_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 23 b) :=
  xc m 20 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_21_4 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 4 b = X m 4 b * X m 21 a * X m 15 (a*b) :=
  xs m 21 4 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_21_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 5 b) :=
  xc m 21 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_21_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 23 b) :=
  xc m 21 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem chunk_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 0) * (X m 5 (v 1) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 2) * (v 3)) * (X m 9 (v 4) * (X m 8 (v 5) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 22 (v 8) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))) =
      X m 4 (v 0) * (X m 5 (v 1) * (X m 10 ((v 2) * (v 6)) * (X m 12 (v 6) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 22 (v 8) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_9_8 m (v 4) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [add_suffix m 8 ((v 2) * (v 3)) (v 5),
      show ((v 2) * (v 3)) + (v 5) = ((v 5) + ((v 2) * (v 3))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_9_12 m (v 4) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_8_12 m ((v 5) + ((v 2) * (v 3))) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_7_12 m (v 3) (v 6)).left_comm]
  have h5 : X m 6 (v 2) * X m 12 (v 6) = X m 12 (v 6) * X m 6 (v 2) * X m 10 ((v 2) * (v 6)) := by
    have h := s_6_12 m (v 2) (v 6)
    rw [show (v 2) * (v 6) = ((v 2) * (v 6)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2]
    rw [swap_suffix h5]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_6_10 m (v 2) ((v 2) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [(c_12_10 m (v 6) ((v 2) * (v 6))).left_comm]

private theorem chunk_1 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 0) * (X m 5 (v 1) * (X m 10 ((v 2) * (v 6)) * (X m 12 (v 6) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 22 (v 8) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))) =
      X m 4 (v 0) * (X m 5 (v 1) * (X m 10 ((v 2) * (v 6)) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 14 ((v 6) * (v 7)) * (X m 22 (v 8) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m (v 4) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_8_13 m ((v 5) + ((v 2) * (v 3))) (v 7)).left_comm]
  have h2 : X m 7 (v 3) * X m 13 (v 7) = X m 13 (v 7) * X m 7 (v 3) * X m 11 ((v 3) * (v 7)) := by
    have h := s_7_13 m (v 3) (v 7)
    rw [show (v 3) * (v 7) = ((v 3) * (v 7)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [swap_suffix h2]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_6_13 m (v 2) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_7_11 m (v 3) ((v 3) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_6_11 m (v 2) ((v 3) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_13_11 m (v 7) ((v 3) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_12_11 m (v 6) ((v 3) * (v 7))).left_comm]

private theorem chunk_2 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 0) * (X m 5 (v 1) * (X m 10 ((v 2) * (v 6)) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 14 ((v 6) * (v 7)) * (X m 22 (v 8) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))) =
      X m 4 (v 0) * (X m 5 (v 1) * (X m 10 ((v 2) * (v 6)) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 22 (v 8) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 20 ((v 3) * (v 8)) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 15 ((v 4) * (v 8)) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m (v 4) ((v 6) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m ((v 5) + ((v 2) * (v 3))) ((v 6) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_14 m (v 3) ((v 6) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_6_14 m (v 2) ((v 6) * (v 7))).left_comm]
  have h4 : X m 9 (v 4) * X m 22 (v 8) = X m 22 (v 8) * X m 9 (v 4) * X m 15 ((v 4) * (v 8)) := by
    have h := s_9_22 m (v 4) (v 8)
    rw [show (v 4) * (v 8) = ((v 4) * (v 8)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_22 m ((v 5) + ((v 2) * (v 3))) (v 8)).left_comm]
  have h6 : X m 7 (v 3) * X m 22 (v 8) = X m 22 (v 8) * X m 7 (v 3) * X m 20 ((v 3) * (v 8)) * X m 16 ((v 8) * ((v 3) ^ 2)) := by
    have h := s_7_22 m (v 3) (v 8)
    rw [show (v 3) * (v 8) = ((v 3) * (v 8)) by ring, show (v 8) * (v 3) ^ 2 = ((v 8) * ((v 3) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h6]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_22 m (v 2) (v 8)).left_comm]

private theorem chunk_3 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 0) * (X m 5 (v 1) * (X m 10 ((v 2) * (v 6)) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 22 (v 8) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 20 ((v 3) * (v 8)) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 15 ((v 4) * (v 8)) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 21 ((v 6) * (v 8)) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 20 ((v 3) * (v 8)) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 15 ((v 4) * (v 8)) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_14_22 m ((v 6) * (v 7)) (v 8)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_13_22 m (v 7) (v 8)).left_comm]
  have h2 : X m 12 (v 6) * X m 22 (v 8) = X m 22 (v 8) * X m 12 (v 6) * X m 21 ((v 6) * (v 8)) := by
    have h := s_12_22 m (v 6) (v 8)
    rw [show (v 6) * (v 8) = ((v 6) * (v 8)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [swap_suffix h2]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_11_22 m ((v 3) * (v 7)) (v 8)).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [(c_10_22 m ((v 2) * (v 6)) (v 8)).left_comm]
  have h5 : X m 5 (v 1) * X m 22 (v 8) = X m 22 (v 8) * X m 5 (v 1) * X m 17 ((v 1) * (v 8)) * X m 10 ((v 8) * ((v 1) ^ 2)) := by
    have h := s_5_22 m (v 1) (v 8)
    rw [show (v 1) * (v 8) = ((v 1) * (v 8)) by ring, show (v 8) * (v 1) ^ 2 = ((v 8) * ((v 1) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2]
    rw [swap_suffix_two h5]
  conv_lhs =>
    rw [(c_4_22 m (v 0) (v 8)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [add_suffix m 10 ((v 8) * ((v 1) ^ 2)) ((v 2) * (v 6)),
      show ((v 8) * ((v 1) ^ 2)) + ((v 2) * (v 6)) = (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) by abel]

private theorem chunk_4 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 21 ((v 6) * (v 8)) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 20 ((v 3) * (v 8)) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 15 ((v 4) * (v 8)) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 20 ((v 3) * (v 8)) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 21 ((v 6) * (v 8)) * (X m 6 (v 2) * (X m 15 ((v 2) * (v 8) * ((v 3) ^ 2)) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 15 ((v 4) * (v 8)) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_13 m ((v 6) * (v 8)) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_14 m ((v 6) * (v 8)) ((v 6) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_20 m (v 3) ((v 3) * (v 8))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_20 m (v 2) ((v 3) * (v 8))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_20 m ((v 6) * (v 8)) ((v 3) * (v 8))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_16 m (v 3) ((v 8) * ((v 3) ^ 2))).left_comm]
  have h6 : X m 6 (v 2) * X m 16 ((v 8) * ((v 3) ^ 2)) = X m 16 ((v 8) * ((v 3) ^ 2)) * X m 6 (v 2) * X m 15 ((v 2) * (v 8) * ((v 3) ^ 2)) := by
    have h := s_6_16 m (v 2) ((v 8) * ((v 3) ^ 2))
    rw [show (v 2) * ((v 8) * ((v 3) ^ 2)) = ((v 2) * (v 8) * ((v 3) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h6]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_16 m ((v 6) * (v 8)) ((v 8) * ((v 3) ^ 2))).left_comm]

private theorem chunk_5 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 20 ((v 3) * (v 8)) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 21 ((v 6) * (v 8)) * (X m 6 (v 2) * (X m 15 ((v 2) * (v 8) * ((v 3) ^ 2)) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 15 ((v 4) * (v 8)) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 20 ((v 3) * (v 8)) * (X m 21 ((v 6) * (v 8)) * (X m 15 ((v 2) * (v 8) * ((v 3) ^ 2)) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 15 ((v 4) * (v 8)) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_16 m ((v 3) * (v 8)) ((v 8) * ((v 3) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_16 m ((v 6) * (v 7)) ((v 8) * ((v 3) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_16 m (v 7) ((v 8) * ((v 3) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_12_16 m (v 6) ((v 8) * ((v 3) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_11_16 m ((v 3) * (v 7)) ((v 8) * ((v 3) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_10_16 m (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) ((v 8) * ((v 3) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_17_16 m ((v 1) * (v 8)) ((v 8) * ((v 3) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_15 m (v 2) ((v 2) * (v 8) * ((v 3) ^ 2))).left_comm]

private theorem chunk_6 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 20 ((v 3) * (v 8)) * (X m 21 ((v 6) * (v 8)) * (X m 15 ((v 2) * (v 8) * ((v 3) ^ 2)) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 15 ((v 4) * (v 8)) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 15 ((v 2) * (v 8) * ((v 3) ^ 2)) * (X m 15 ((v 4) * (v 8)) * (X m 20 ((v 3) * (v 8)) * (X m 21 ((v 6) * (v 8)) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_15 m ((v 6) * (v 8)) ((v 2) * (v 8) * ((v 3) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_15 m ((v 3) * (v 8)) ((v 2) * (v 8) * ((v 3) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m (v 4) ((v 4) * (v 8))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m ((v 5) + ((v 2) * (v 3))) ((v 4) * (v 8))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_15 m (v 3) ((v 4) * (v 8))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_15 m (v 2) ((v 4) * (v 8))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_15 m ((v 6) * (v 8)) ((v 4) * (v 8))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_15 m ((v 3) * (v 8)) ((v 4) * (v 8))).left_comm]

private theorem chunk_7 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 15 ((v 2) * (v 8) * ((v 3) ^ 2)) * (X m 15 ((v 4) * (v 8)) * (X m 20 ((v 3) * (v 8)) * (X m 21 ((v 6) * (v 8)) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 23 (v 9) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 ((v 3) * (v 8)) * (X m 21 ((v 6) * (v 8)) * (X m 6 (v 2) * (X m 17 ((v 2) * (v 9)) * (X m 21 ((v 2) * ((v 9) ^ 2)) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 9 (v 4) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 2) * (v 8) * ((v 3) ^ 2)) ((v 4) * (v 8)),
      show ((v 2) * (v 8) * ((v 3) ^ 2)) + ((v 4) * (v 8)) = (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_23 m (v 4) (v 9)).left_comm]
  have h2 : X m 8 ((v 5) + ((v 2) * (v 3))) * X m 23 (v 9) = X m 23 (v 9) * X m 8 ((v 5) + ((v 2) * (v 3))) * X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) := by
    have h := s_8_23 m ((v 5) + ((v 2) * (v 3))) (v 9)
    rw [show ((v 5) + ((v 2) * (v 3))) * (v 9) = (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h2]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_23 m (v 3) (v 9)).left_comm]
  have h4 : X m 6 (v 2) * X m 23 (v 9) = X m 23 (v 9) * X m 6 (v 2) * X m 17 ((v 2) * (v 9)) * X m 21 ((v 2) * ((v 9) ^ 2)) := by
    have h := s_6_23 m (v 2) (v 9)
    rw [show (v 2) * (v 9) = ((v 2) * (v 9)) by ring, show (v 2) * (v 9) ^ 2 = ((v 2) * ((v 9) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_23 m ((v 6) * (v 8)) (v 9)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_23 m ((v 3) * (v 8)) (v 9)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_23 m (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) (v 9)).left_comm]

private theorem chunk_8 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 23 (v 9) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 ((v 3) * (v 8)) * (X m 21 ((v 6) * (v 8)) * (X m 6 (v 2) * (X m 17 ((v 2) * (v 9)) * (X m 21 ((v 2) * ((v 9) ^ 2)) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 9 (v 4) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 4 (v 0) * (X m 23 (v 9) * (X m 5 (v 1) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 20 ((v 7) * (v 9)) * (X m 14 ((v 6) * (v 7)) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 ((v 3) * (v 8)) * (X m 21 ((v 6) * (v 8)) * (X m 6 (v 2) * (X m 17 ((v 2) * (v 9)) * (X m 21 ((v 2) * ((v 9) ^ 2)) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 9 (v 4) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_23 m ((v 6) * (v 7)) (v 9)).left_comm]
  have h1 : X m 13 (v 7) * X m 23 (v 9) = X m 23 (v 9) * X m 13 (v 7) * X m 20 ((v 7) * (v 9)) := by
    have h := s_13_23 m (v 7) (v 9)
    rw [show (v 7) * (v 9) = ((v 7) * (v 9)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h1]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_23 m (v 6) (v 9)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_11_23 m ((v 3) * (v 7)) (v 9)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_10_23 m (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) (v 9)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_17_23 m ((v 1) * (v 8)) (v 9)).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_16_23 m ((v 8) * ((v 3) ^ 2)) (v 9)).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [(c_5_23 m (v 1) (v 9)).left_comm]

private theorem chunk_9 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 4 (v 0) * (X m 23 (v 9) * (X m 5 (v 1) * (X m 16 ((v 8) * ((v 3) ^ 2)) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 20 ((v 7) * (v 9)) * (X m 14 ((v 6) * (v 7)) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 ((v 3) * (v 8)) * (X m 21 ((v 6) * (v 8)) * (X m 6 (v 2) * (X m 17 ((v 2) * (v 9)) * (X m 21 ((v 2) * ((v 9) ^ 2)) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 9 (v 4) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 0) * (v 9)) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 20 ((v 7) * (v 9)) * (X m 14 ((v 6) * (v 7)) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 ((v 3) * (v 8)) * (X m 21 ((v 6) * (v 8)) * (X m 6 (v 2) * (X m 17 ((v 2) * (v 9)) * (X m 21 ((v 2) * ((v 9) ^ 2)) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 9 (v 4) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))))))) := by
  have h0 : X m 4 (v 0) * X m 23 (v 9) = X m 23 (v 9) * X m 4 (v 0) * X m 11 ((v 0) * (v 9)) * X m 16 ((v 0) * ((v 9) ^ 2)) := by
    have h := s_4_23 m (v 0) (v 9)
    rw [show (v 0) * (v 9) = ((v 0) * (v 9)) by ring, show (v 0) * (v 9) ^ 2 = ((v 0) * ((v 9) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2]
    rw [swap_suffix_two h0]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_11_16 m ((v 0) * (v 9)) ((v 0) * ((v 9) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_11_5 m ((v 0) * (v 9)) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_16_5 m ((v 0) * ((v 9) ^ 2)) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_11_16 m ((v 0) * (v 9)) ((v 8) * ((v 3) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [add_suffix m 16 ((v 0) * ((v 9) ^ 2)) ((v 8) * ((v 3) ^ 2)),
      show ((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2)) = (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_11_17 m ((v 0) * (v 9)) ((v 1) * (v 8))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_11_10 m ((v 0) * (v 9)) (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2)))).left_comm]

private theorem chunk_10 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 0) * (v 9)) * (X m 11 ((v 3) * (v 7)) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 20 ((v 7) * (v 9)) * (X m 14 ((v 6) * (v 7)) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 ((v 3) * (v 8)) * (X m 21 ((v 6) * (v 8)) * (X m 6 (v 2) * (X m 17 ((v 2) * (v 9)) * (X m 21 ((v 2) * ((v 9) ^ 2)) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 9 (v 4) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 (((v 0) * (v 9)) + ((v 3) * (v 7))) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 17 ((v 2) * (v 9)) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 ((v 6) * (v 8)) * (X m 6 (v 2) * (X m 21 ((v 2) * ((v 9) ^ 2)) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 9 (v 4) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 11 ((v 0) * (v 9)) ((v 3) * (v 7)),
      show ((v 0) * (v 9)) + ((v 3) * (v 7)) = (((v 0) * (v 9)) + ((v 3) * (v 7))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_14 m ((v 7) * (v 9)) ((v 6) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_15 m ((v 7) * (v 9)) (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 20 ((v 7) * (v 9)) ((v 3) * (v 8)),
      show ((v 7) * (v 9)) + ((v 3) * (v 8)) = (((v 3) * (v 8)) + ((v 7) * (v 9))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_17 m (v 2) ((v 2) * (v 9))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_17 m ((v 6) * (v 8)) ((v 2) * (v 9))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_17 m (((v 3) * (v 8)) + ((v 7) * (v 9))) ((v 2) * (v 9))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_17 m (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) ((v 2) * (v 9))).left_comm]

private theorem chunk_11 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 ((v 1) * (v 8)) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 (((v 0) * (v 9)) + ((v 3) * (v 7))) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 17 ((v 2) * (v 9)) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 ((v 6) * (v 8)) * (X m 6 (v 2) * (X m 21 ((v 2) * ((v 9) ^ 2)) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 9 (v 4) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 (((v 0) * (v 9)) + ((v 3) * (v 7))) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 9 (v 4) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_17 m ((v 6) * (v 7)) ((v 2) * (v 9))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_17 m (v 7) ((v 2) * (v 9))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_17 m (v 6) ((v 2) * (v 9))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_11_17 m (((v 0) * (v 9)) + ((v 3) * (v 7))) ((v 2) * (v 9))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_10_17 m (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) ((v 2) * (v 9))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [add_suffix m 17 ((v 1) * (v 8)) ((v 2) * (v 9)),
      show ((v 1) * (v 8)) + ((v 2) * (v 9)) = (((v 1) * (v 8)) + ((v 2) * (v 9))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_21 m (v 2) ((v 2) * ((v 9) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 21 ((v 6) * (v 8)) ((v 2) * ((v 9) ^ 2)),
      show ((v 6) * (v 8)) + ((v 2) * ((v 9) ^ 2)) = (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) by abel]

private theorem chunk_12 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 (((v 0) * (v 9)) + ((v 3) * (v 7))) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 9 (v 4) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 (((v 0) * (v 9)) + ((v 3) * (v 7))) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 (((v 5) * (v 9)) + ((v 6) * (v 7)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 14 ((v 6) * (v 7)) * (X m 9 (v 4) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m ((v 5) + ((v 2) * (v 3))) (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_14 m (v 3) (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_14 m (v 2) (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_14 m (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_14 m (((v 3) * (v 8)) + ((v 7) * (v 9))) (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 ((v 6) * (v 7)) (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))),
      show ((v 6) * (v 7)) + (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) = (((v 5) * (v 9)) + ((v 6) * (v 7)) + ((v 2) * (v 3) * (v 9))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m (v 4) ((v 6) * (v 7))).left_comm]

private theorem chunk_13 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 (((v 0) * (v 9)) + ((v 3) * (v 7))) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 (((v 5) * (v 9)) + ((v 6) * (v 7)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 14 ((v 6) * (v 7)) * (X m 9 (v 4) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 (((v 0) * (v 9)) + ((v 3) * (v 7))) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 13 (v 7) * (X m 9 (v 4) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m ((v 5) + ((v 2) * (v 3))) ((v 6) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_14 m (v 3) ((v 6) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_14 m (v 2) ((v 6) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_14 m (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) ((v 6) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_14 m (((v 3) * (v 8)) + ((v 7) * (v 9))) ((v 6) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) ((v 6) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 (((v 5) * (v 9)) + ((v 6) * (v 7)) + ((v 2) * (v 3) * (v 9))) ((v 6) * (v 7)),
      show (((v 5) * (v 9)) + ((v 6) * (v 7)) + ((v 2) * (v 3) * (v 9))) + ((v 6) * (v 7)) = (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m (v 4) (v 7)).left_comm]

private theorem chunk_14 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 (((v 0) * (v 9)) + ((v 3) * (v 7))) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 13 (v 7) * (X m 9 (v 4) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 (((v 0) * (v 9)) + ((v 3) * (v 7))) * (X m 12 (v 6) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 11 ((v 3) * (v 7)) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_13 m ((v 5) + ((v 2) * (v 3))) (v 7)).left_comm]
  have h1 : X m 7 (v 3) * X m 13 (v 7) = X m 13 (v 7) * X m 7 (v 3) * X m 11 ((v 3) * (v 7)) := by
    have h := s_7_13 m (v 3) (v 7)
    rw [show (v 3) * (v 7) = ((v 3) * (v 7)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h1]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_13 m (v 2) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_13 m (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_13 m (((v 3) * (v 8)) + ((v 7) * (v 9))) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_13 m (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_13 m (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 13 (v 7) (v 7),
      show (v 7) + (v 7) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]

private theorem chunk_15 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 (((v 0) * (v 9)) + ((v 3) * (v 7))) * (X m 12 (v 6) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 11 ((v 3) * (v 7)) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 0) * (v 9)) * (X m 12 (v 6) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_11 m (v 3) ((v 3) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_11 m (v 2) ((v 3) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_11 m (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) ((v 3) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_11 m (((v 3) * (v 8)) + ((v 7) * (v 9))) ((v 3) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_11 m (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) ((v 3) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_11 m (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) ((v 3) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_11 m (v 6) ((v 3) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 11 (((v 0) * (v 9)) + ((v 3) * (v 7))) ((v 3) * (v 7)),
      show (((v 0) * (v 9)) + ((v 3) * (v 7))) + ((v 3) * (v 7)) = ((v 0) * (v 9)) by abel_nf; simp [CharTwo.two_eq_zero]]

private theorem chunk_16 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 0) * (v 9)) * (X m 12 (v 6) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 0) * (v 9)) * (X m 12 (v 6) * (X m 12 (v 6) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 10 ((v 2) * (v 6)) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_12 m (v 4) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_12 m ((v 5) + ((v 2) * (v 3))) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_12 m (v 3) (v 6)).left_comm]
  have h3 : X m 6 (v 2) * X m 12 (v 6) = X m 12 (v 6) * X m 6 (v 2) * X m 10 ((v 2) * (v 6)) := by
    have h := s_6_12 m (v 2) (v 6)
    rw [show (v 2) * (v 6) = ((v 2) * (v 6)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h3]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_12 m (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_12 m (((v 3) * (v 8)) + ((v 7) * (v 9))) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_12 m (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_12 m (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) (v 6)).left_comm]

private theorem chunk_17 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) * (X m 11 ((v 0) * (v 9)) * (X m 12 (v 6) * (X m 12 (v 6) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 10 ((v 2) * (v 6)) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 ((v 8) * ((v 1) ^ 2)) * (X m 11 ((v 0) * (v 9)) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 12 (v 6) (v 6),
      show (v 6) + (v 6) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_10 m (v 2) ((v 2) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_10 m (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) ((v 2) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_10 m (((v 3) * (v 8)) + ((v 7) * (v 9))) ((v 2) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_10 m (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) ((v 2) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_10 m (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) ((v 2) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_11_10 m ((v 0) * (v 9)) ((v 2) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [add_suffix m 10 (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) ((v 2) * (v 6)),
      show (((v 2) * (v 6)) + ((v 8) * ((v 1) ^ 2))) + ((v 2) * (v 6)) = ((v 8) * ((v 1) ^ 2)) by abel_nf; simp [CharTwo.two_eq_zero]]

private theorem chunk_18 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 ((v 8) * ((v 1) ^ 2)) * (X m 11 ((v 0) * (v 9)) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 5) + ((v 2) * (v 3))) * (X m 9 (v 4) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1))))))))))))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 ((v 8) * ((v 1) ^ 2)) * (X m 11 ((v 0) * (v 9)) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 5 (v 1) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 14 (((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 4 (v 0) * (1))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (v 4) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 ((v 5) + ((v 2) * (v 3))) (v 5),
      show ((v 5) + ((v 2) * (v 3))) + (v 5) = ((v 2) * (v 3)) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 (v 4) (v 4),
      show (v 4) + (v 4) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 ((v 2) * (v 3)) ((v 2) * (v 3)),
      show ((v 2) * (v 3)) + ((v 2) * (v 3)) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 7 (v 3) (v 3),
      show (v 3) + (v 3) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 6 (v 2) (v 2),
      show (v 2) + (v 2) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_5 m (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) (v 1)).left_comm]
  have h7 : X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * X m 5 (v 1) = X m 5 (v 1) * X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * X m 14 (((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9))) := by
    have h := s_20_5 m (((v 3) * (v 8)) + ((v 7) * (v 9))) (v 1)
    rw [show (((v 3) * (v 8)) + ((v 7) * (v 9))) * (v 1) = (((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h7]

private theorem chunk_19 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 5 (v 1) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 ((v 8) * ((v 1) ^ 2)) * (X m 11 ((v 0) * (v 9)) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 5 (v 1) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 14 (((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 4 (v 0) * (1))))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 ((v 8) * ((v 1) ^ 2)) * (X m 11 ((v 0) * (v 9)) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 14 (((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 4 (v 0) * (1))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_5 m (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_5 m (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_11_5 m ((v 0) * (v 9)) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_10_5 m ((v 8) * ((v 1) ^ 2)) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_17_5 m (((v 1) * (v 8)) + ((v 2) * (v 9))) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_16_5 m (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [add_suffix m 5 (v 1) (v 1),
      show (v 1) + (v 1) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_14 m (((v 3) * (v 8)) + ((v 7) * (v 9))) (((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9)))).left_comm]

private theorem chunk_20 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 ((v 8) * ((v 1) ^ 2)) * (X m 11 ((v 0) * (v 9)) * (X m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 14 (((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 4 (v 0) * (1))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 4 (v 0) * (X m 10 ((v 8) * ((v 1) ^ 2)) * (X m 11 ((v 0) * (v 9)) * (X m 14 (((v 5) * (v 9)) + ((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 15 (((v 0) * (v 2) * ((v 9) ^ 2)) + ((v 0) * (v 6) * (v 8))) * (1))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) (((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) (((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9))),
      show (((v 5) * (v 9)) + ((v 2) * (v 3) * (v 9))) + (((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9))) = (((v 5) * (v 9)) + ((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9)) + ((v 2) * (v 3) * (v 9))) by abel]
  have h2 : X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * X m 4 (v 0) = X m 4 (v 0) * X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * X m 15 (((v 0) * (v 2) * ((v 9) ^ 2)) + ((v 0) * (v 6) * (v 8))) := by
    have h := s_21_4 m (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) (v 0)
    rw [show (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (v 0) = (((v 0) * (v 2) * ((v 9) ^ 2)) + ((v 0) * (v 6) * (v 8))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h2]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_4 m (((v 3) * (v 8)) + ((v 7) * (v 9))) (v 0)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_4 m (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) (v 0)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_4 m (((v 5) * (v 9)) + ((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9)) + ((v 2) * (v 3) * (v 9))) (v 0)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_11_4 m ((v 0) * (v 9)) (v 0)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_10_4 m ((v 8) * ((v 1) ^ 2)) (v 0)).left_comm]

private theorem chunk_21 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 22 (v 8) * (X m 23 (v 9) * (X m 4 (v 0) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 4 (v 0) * (X m 10 ((v 8) * ((v 1) ^ 2)) * (X m 11 ((v 0) * (v 9)) * (X m 14 (((v 5) * (v 9)) + ((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (X m 15 (((v 0) * (v 2) * ((v 9) ^ 2)) + ((v 0) * (v 6) * (v 8))) * (1))))))))))))) =
      X m 22 (v 8) * (X m 23 (v 9) * (X m 16 (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) * (X m 17 (((v 1) * (v 8)) + ((v 2) * (v 9))) * (X m 10 ((v 8) * ((v 1) ^ 2)) * (X m 11 ((v 0) * (v 9)) * (X m 14 (((v 5) * (v 9)) + ((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9)) + ((v 2) * (v 3) * (v 9))) * (X m 15 (((v 4) * (v 8)) + ((v 0) * (v 2) * ((v 9) ^ 2)) + ((v 0) * (v 6) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) * (X m 20 (((v 3) * (v 8)) + ((v 7) * (v 9))) * (X m 21 (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) * (1)))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_17_4 m (((v 1) * (v 8)) + ((v 2) * (v 9))) (v 0)).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_16_4 m (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))) (v 0)).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [add_suffix m 4 (v 0) (v 0),
      show (v 0) + (v 0) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_15 m (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))) (((v 0) * (v 2) * ((v 9) ^ 2)) + ((v 0) * (v 6) * (v 8)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_15 m (((v 3) * (v 8)) + ((v 7) * (v 9))) (((v 0) * (v 2) * ((v 9) ^ 2)) + ((v 0) * (v 6) * (v 8)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) (((v 0) * (v 2) * ((v 9) ^ 2)) + ((v 0) * (v 6) * (v 8))),
      show (((v 4) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) + (((v 0) * (v 2) * ((v 9) ^ 2)) + ((v 0) * (v 6) * (v 8))) = (((v 4) * (v 8)) + ((v 0) * (v 2) * ((v 9) ^ 2)) + ((v 0) * (v 6) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))) by abel]

/-- The literal split-word conjugation; the paired parameters are independent. -/
theorem conjugator_split (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 0) * (X m 5 (v 1) * (X m 6 (v 2) * (X m 7 (v 3) * (X m 8 ((v 2) * (v 3)) * (X m 9 (v 4) * (X m 8 (v 5) * (X m 12 (v 6) * (X m 13 (v 7) * (X m 14 ((v 6) * (v 7)) * (X m 22 (v 8) * (X m 23 (v 9) * (X m 14 ((v 6) * (v 7)) * (X m 13 (v 7) * (X m 12 (v 6) * (X m 8 (v 5) * (X m 9 (v 4) * (X m 8 ((v 2) * (v 3)) * (X m 7 (v 3) * (X m 6 (v 2) * (X m 5 (v 1) * (X m 4 (v 0) * (1)))))))))))))))))))))) =
      splitWord m ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ((v 8) * ((v 1) ^ 2)), ((v 0) * (v 9)), 0, 0, (((v 5) * (v 9)) + ((v 1) * (v 3) * (v 8)) + ((v 1) * (v 7) * (v 9)) + ((v 2) * (v 3) * (v 9))), (((v 4) * (v 8)) + ((v 0) * (v 2) * ((v 9) ^ 2)) + ((v 0) * (v 6) * (v 8)) + ((v 2) * (v 8) * ((v 3) ^ 2))), (((v 0) * ((v 9) ^ 2)) + ((v 8) * ((v 3) ^ 2))), (((v 1) * (v 8)) + ((v 2) * (v 9))), 0, 0, (((v 3) * (v 8)) + ((v 7) * (v 9))), (((v 2) * ((v 9) ^ 2)) + ((v 6) * (v 8))), (v 8), (v 9)] := by
  have h := (((((chunk_0 m v).trans (chunk_1 m v)).trans ((chunk_2 m v).trans ((chunk_3 m v).trans (chunk_4 m v)))).trans (((chunk_5 m v).trans ((chunk_6 m v).trans (chunk_7 m v))).trans ((chunk_8 m v).trans ((chunk_9 m v).trans (chunk_10 m v))))).trans ((((chunk_11 m v).trans (chunk_12 m v)).trans ((chunk_13 m v).trans ((chunk_14 m v).trans (chunk_15 m v)))).trans (((chunk_16 m v).trans ((chunk_17 m v).trans (chunk_18 m v))).trans ((chunk_19 m v).trans ((chunk_20 m v).trans (chunk_21 m v))))))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.Collection
