module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords
public import Mathlib.Tactic.Abel

/-!
# Split coordinates of squares in the Ree C section

Removing split roots 22 and 23 removes the relative root X₈. Collecting the
square then gives coordinates v₀v₁² and v₁₈v₁₉² at split roots 3 and 21.
Every exchange below uses the checked F₄ matrix relations; coordinate
uniqueness detects these two parameters. The adjacent `source/generate.py`
is an untrusted proof-writing tool, using the preserved OuterElimination
collector. All its output is checked by ordinary Lean proofs.

Source: GLS3 Table 2.4, 2.4.5(d) and Lemma 3.3.9,
`refs/KGroup/GLS3/chapter2.tex` and `chapter3.tex`.
-/

public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.Replacement.EndpointSquares.Collection
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

private theorem s_1_0 (m : ℕ) (a b : CoefficientField m) :
    X m 1 a * X m 0 b = X m 0 b * X m 1 a * X m 2 (a*b) * X m 3 (b*a^2) := by
  simpa only [mul_comm] using xb m 0 1 2 3 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_1_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 1 a) (X m 4 b) :=
  xc m 1 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_1_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 1 a) (X m 5 b) :=
  xc m 1 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_3_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 0 b) :=
  xc m 3 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_3_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 1 b) :=
  xc m 3 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem s_3_16 (m : ℕ) (a b : CoefficientField m) :
    X m 3 a * X m 16 b = X m 16 b * X m 3 a * X m 9 (a*b) :=
  xs m 3 16 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_3_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 3 a) (X m 17 b) :=
  xc m 3 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_5_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 5 a) (X m 4 b) :=
  xc m 5 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_6_0 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 0 b = X m 0 b * X m 6 a * X m 4 (a*b) :=
  xs m 6 0 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_6_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 1 b) :=
  xc m 6 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem s_6_16 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 16 b = X m 16 b * X m 6 a * X m 15 (a*b) :=
  xs m 6 16 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_6_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 17 b) :=
  xc m 6 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 18 b) :=
  xc m 6 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 19 b) :=
  xc m 6 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 20 b) :=
  xc m 6 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 21 b) :=
  xc m 6 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 0 b) :=
  xc m 7 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_7_1 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 1 b = X m 1 b * X m 7 a * X m 5 (a*b) :=
  xs m 7 1 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

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

private theorem c_7_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 16 b) :=
  xc m 7 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_7_17 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 17 b = X m 17 b * X m 7 a * X m 14 (a*b) :=
  xs m 7 17 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_7_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 18 b) :=
  xc m 7 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 19 b) :=
  xc m 7 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 20 b) :=
  xc m 7 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_21 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 21 b) :=
  xc m 7 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_12_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 0 b) :=
  xc m 12 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 1 b) :=
  xc m 12 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_12_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 16 b) :=
  xc m 12 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 17 b) :=
  xc m 12 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 0 b) :=
  xc m 13 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 1 b) :=
  xc m 13 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_13_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 16 b) :=
  xc m 13 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 17 b) :=
  xc m 13 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem c_18_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 0 b) :=
  xc m 18 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_18_1 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 1 b = X m 1 b * X m 18 a * X m 13 (a*b) * X m 6 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 18 1 13 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 13 (a*b)) (xx m 6 (a*b^2))
    (xc m 13 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

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

private theorem s_19_0 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 0 b = X m 0 b * X m 19 a * X m 7 (a*b) * X m 12 (b*a^2) := by
  simpa only [mul_comm] using xb m 0 19 7 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_19_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 1 b) :=
  xc m 19 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

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

private theorem s_19_18 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 18 b = X m 18 b * X m 19 a * X m 20 (a*b) * X m 21 (b*a^2) := by
  simpa only [mul_comm] using xb m 18 19 20 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_20_0 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 20 a) (X m 0 b) :=
  xc m 20 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_20_1 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 1 b = X m 1 b * X m 20 a * X m 17 (a*b) :=
  xs m 20 1 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

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

private theorem s_21_3 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 3 b = X m 3 b * X m 21 a * X m 10 (a*b) :=
  xs m 21 3 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

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

private theorem c_21_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 18 b) :=
  xc m 21 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 19 b) :=
  xc m 21 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_21_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 20 b) :=
  xc m 21 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem chunk_0 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) =
      X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 4 (v 4) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 10 ((v 4) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_4 m (v 9) (v 4)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_4 m (v 8) (v 4)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_4 m (v 7) (v 4)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_4 m (v 6) (v 4)).left_comm]
  have h4 : X m 21 (v 21) * X m 4 (v 4) = X m 4 (v 4) * X m 21 (v 21) * X m 15 ((v 21) * (v 4)) := by
    have h := s_21_4 m (v 21) (v 4)
    rw [show (v 21) * (v 4) = ((v 21) * (v 4)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_4 m (v 20) (v 4)).left_comm]
  have h6 : X m 19 (v 19) * X m 4 (v 4) = X m 4 (v 4) * X m 19 (v 19) * X m 8 ((v 19) * (v 4)) * X m 10 ((v 4) * ((v 19) ^ 2)) := by
    have h := s_19_4 m (v 19) (v 4)
    rw [show (v 19) * (v 4) = ((v 19) * (v 4)) by ring, show (v 4) * (v 19) ^ 2 = ((v 4) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h6]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_4 m (v 18) (v 4)).left_comm]

private theorem chunk_1 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 4 (v 4) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 10 ((v 4) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))))))) =
      X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 4 (v 4) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 9 ((v 12) * (v 4)) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 10 ((v 4) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_4 m (v 15) (v 4)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_4 m (v 14) (v 4)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_4 m (v 13) (v 4)).left_comm]
  have h3 : X m 12 (v 12) * X m 4 (v 4) = X m 4 (v 4) * X m 12 (v 12) * X m 9 ((v 12) * (v 4)) := by
    have h := s_12_4 m (v 12) (v 4)
    rw [show (v 12) * (v 4) = ((v 12) * (v 4)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h3]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_4 m (v 3) (v 4)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_2_4 m (v 2) (v 4)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_1_4 m (v 1) (v 4)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_0_4 m (v 0) (v 4)).left_comm]

private theorem chunk_2 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 4 (v 4) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 9 ((v 12) * (v 4)) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 10 ((v 4) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))))))) =
      X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 9 ((v 12) * (v 4)) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 10 ((v 4) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_11_4 m (v 11) (v 4)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_10_4 m (v 10) (v 4)).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_17_4 m (v 17) (v 4)).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [(c_16_4 m (v 16) (v 4)).left_comm]
  conv_lhs =>
    enter [2]
    rw [(c_5_4 m (v 5) (v 4)).left_comm]
  conv_lhs =>
    rw [add_suffix m 4 (v 4) (v 4),
      show (v 4) + (v 4) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m ((v 12) * (v 4)) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m ((v 12) * (v 4)) (v 14)).left_comm]

private theorem chunk_3 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 9 ((v 12) * (v 4)) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 10 ((v 4) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))))) =
      X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 10 ((v 4) * ((v 19) ^ 2)) * (X m 18 (v 18) * (X m 15 ((v 18) * (v 4) * ((v 19) ^ 2)) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 9 ((v 12) * (v 4)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m ((v 12) * (v 4)) (v 15)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m ((v 12) * (v 4)) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m ((v 12) * (v 4)) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m ((v 12) * (v 4)) ((v 19) * (v 4))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_10 m ((v 12) * (v 4)) ((v 4) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_10 m ((v 19) * (v 4)) ((v 4) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_10 m (v 19) ((v 4) * ((v 19) ^ 2))).left_comm]
  have h7 : X m 18 (v 18) * X m 10 ((v 4) * ((v 19) ^ 2)) = X m 10 ((v 4) * ((v 19) ^ 2)) * X m 18 (v 18) * X m 15 ((v 18) * (v 4) * ((v 19) ^ 2)) := by
    have h := s_18_10 m (v 18) ((v 4) * ((v 19) ^ 2))
    rw [show (v 18) * ((v 4) * ((v 19) ^ 2)) = ((v 18) * (v 4) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h7]

private theorem chunk_4 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 10 ((v 4) * ((v 19) ^ 2)) * (X m 18 (v 18) * (X m 15 ((v 18) * (v 4) * ((v 19) ^ 2)) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 9 ((v 12) * (v 4)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))))))) =
      X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 10 ((v 4) * ((v 19) ^ 2)) * (X m 0 (v 0) * (X m 9 ((v 0) * (v 4) * ((v 19) ^ 2)) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 15 ((v 18) * (v 4) * ((v 19) ^ 2)) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 9 ((v 12) * (v 4)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_10 m (v 15) ((v 4) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_10 m (v 14) ((v 4) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_10 m (v 13) ((v 4) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_10 m (v 12) ((v 4) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_10 m (v 3) ((v 4) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_2_10 m (v 2) ((v 4) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_1_10 m (v 1) ((v 4) * ((v 19) ^ 2))).left_comm]
  have h7 : X m 0 (v 0) * X m 10 ((v 4) * ((v 19) ^ 2)) = X m 10 ((v 4) * ((v 19) ^ 2)) * X m 0 (v 0) * X m 9 ((v 0) * (v 4) * ((v 19) ^ 2)) := by
    have h := s_0_10 m (v 0) ((v 4) * ((v 19) ^ 2))
    rw [show (v 0) * ((v 4) * ((v 19) ^ 2)) = ((v 0) * (v 4) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [swap_suffix h7]

private theorem chunk_5 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 10 ((v 4) * ((v 19) ^ 2)) * (X m 0 (v 0) * (X m 9 ((v 0) * (v 4) * ((v 19) ^ 2)) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 15 ((v 18) * (v 4) * ((v 19) ^ 2)) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 9 ((v 12) * (v 4)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))))))) =
      X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 9 ((v 0) * (v 4) * ((v 19) ^ 2)) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 15 ((v 18) * (v 4) * ((v 19) ^ 2)) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 9 ((v 12) * (v 4)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_11_10 m (v 11) ((v 4) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [add_suffix m 10 (v 10) ((v 4) * ((v 19) ^ 2)),
      show (v 10) + ((v 4) * ((v 19) ^ 2)) = ((v 10) + ((v 4) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_9_1 m ((v 0) * (v 4) * ((v 19) ^ 2)) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_2 m ((v 0) * (v 4) * ((v 19) ^ 2)) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_3 m ((v 0) * (v 4) * ((v 19) ^ 2)) (v 3)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_12 m ((v 0) * (v 4) * ((v 19) ^ 2)) (v 12)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m ((v 0) * (v 4) * ((v 19) ^ 2)) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m ((v 0) * (v 4) * ((v 19) ^ 2)) (v 14)).left_comm]

private theorem chunk_6 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 9 ((v 0) * (v 4) * ((v 19) ^ 2)) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 15 ((v 18) * (v 4) * ((v 19) ^ 2)) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 9 ((v 12) * (v 4)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))))))) =
      X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 9 (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m ((v 0) * (v 4) * ((v 19) ^ 2)) (v 15)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m ((v 0) * (v 4) * ((v 19) ^ 2)) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m ((v 0) * (v 4) * ((v 19) ^ 2)) ((v 18) * (v 4) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m (v 18) ((v 18) * (v 4) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 (v 15) ((v 18) * (v 4) * ((v 19) ^ 2)),
      show (v 15) + ((v 18) * (v 4) * ((v 19) ^ 2)) = ((v 15) + ((v 18) * (v 4) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m ((v 0) * (v 4) * ((v 19) ^ 2)) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m ((v 0) * (v 4) * ((v 19) ^ 2)) ((v 19) * (v 4))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 ((v 0) * (v 4) * ((v 19) ^ 2)) ((v 12) * (v 4)),
      show ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 4)) = (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) by abel]

private theorem chunk_7 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 19) * (v 4)) * (X m 9 (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 21) * (v 4)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))))) =
      X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 15 ((v 21) * (v 4)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 ((v 19) * (v 4)) * (X m 9 (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_20 m ((v 19) * (v 4)) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_21 m ((v 19) * (v 4)) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) ((v 21) * (v 4))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m ((v 19) * (v 4)) ((v 21) * (v 4))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_15 m (v 21) ((v 21) * (v 4))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_15 m (v 20) ((v 21) * (v 4))).left_comm]

private theorem chunk_8 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 15 ((v 21) * (v 4)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 ((v 19) * (v 4)) * (X m 9 (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))))) =
      X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 19) * (v 4)) * (X m 8 (v 8) * (X m 9 (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_15 m (v 19) ((v 21) * (v 4))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m (v 18) ((v 21) * (v 4))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 15) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 21) * (v 4)),
      show ((v 15) + ((v 18) * (v 4) * ((v 19) ^ 2))) + ((v 21) * (v 4)) = ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m ((v 19) * (v 4)) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_7 m ((v 19) * (v 4)) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) (v 8)).left_comm]

private theorem chunk_9 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 19) * (v 4)) * (X m 8 (v 8) * (X m 9 (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 9 (v 9) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) =
      X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 5 (v 5) * (X m 20 (v 20) * (X m 14 ((v 20) * (v 5)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 ((v 19) * (v 4)) (v 8),
      show ((v 19) * (v 4)) + (v 8) = ((v 8) + ((v 19) * (v 4))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) (v 9),
      show (((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) + (v 9) = ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_5 m ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_5 m ((v 8) + ((v 19) * (v 4))) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_5 m (v 7) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_5 m (v 6) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_5 m (v 21) (v 5)).left_comm]
  have h7 : X m 20 (v 20) * X m 5 (v 5) = X m 5 (v 5) * X m 20 (v 20) * X m 14 ((v 20) * (v 5)) := by
    have h := s_20_5 m (v 20) (v 5)
    rw [show (v 20) * (v 5) = ((v 20) * (v 5)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h7]

private theorem chunk_10 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 5 (v 5) * (X m 20 (v 20) * (X m 14 ((v 20) * (v 5)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))) =
      X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 5 (v 5) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 8 ((v 13) * (v 5)) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 11 ((v 18) * (v 5)) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 ((v 20) * (v 5)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_5 m (v 19) (v 5)).left_comm]
  have h1 : X m 18 (v 18) * X m 5 (v 5) = X m 5 (v 5) * X m 18 (v 18) * X m 11 ((v 18) * (v 5)) * X m 9 ((v 18) * ((v 5) ^ 2)) := by
    have h := s_18_5 m (v 18) (v 5)
    rw [show (v 18) * (v 5) = ((v 18) * (v 5)) by ring, show (v 18) * (v 5) ^ 2 = ((v 18) * ((v 5) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h1]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_5 m ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_5 m (v 14) (v 5)).left_comm]
  have h4 : X m 13 (v 13) * X m 5 (v 5) = X m 5 (v 5) * X m 13 (v 13) * X m 8 ((v 13) * (v 5)) := by
    have h := s_13_5 m (v 13) (v 5)
    rw [show (v 13) * (v 5) = ((v 13) * (v 5)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_5 m (v 12) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_5 m (v 3) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_2_5 m (v 2) (v 5)).left_comm]

private theorem chunk_11 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 5 (v 5) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 8 ((v 13) * (v 5)) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 11 ((v 18) * (v 5)) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 ((v 20) * (v 5)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 8 ((v 13) * (v 5)) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 11 ((v 18) * (v 5)) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 ((v 20) * (v 5)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_1_5 m (v 1) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_0_5 m (v 0) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_11_5 m (v 11) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_10_5 m ((v 10) + ((v 4) * ((v 19) ^ 2))) (v 5)).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [(c_17_5 m (v 17) (v 5)).left_comm]
  conv_lhs =>
    enter [2]
    rw [(c_16_5 m (v 16) (v 5)).left_comm]
  conv_lhs =>
    rw [add_suffix m 5 (v 5) (v 5),
      show (v 5) + (v 5) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m ((v 13) * (v 5)) (v 14)).left_comm]

private theorem chunk_12 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 8 ((v 13) * (v 5)) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 11 ((v 18) * (v 5)) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 ((v 20) * (v 5)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 11 ((v 18) * (v 5)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 8 ((v 13) * (v 5)) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 ((v 20) * (v 5)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m ((v 13) * (v 5)) ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_18 m ((v 13) * (v 5)) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_11 m ((v 13) * (v 5)) ((v 18) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_11 m (v 18) ((v 18) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_11 m ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 18) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_11 m (v 14) ((v 18) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_11 m (v 13) ((v 18) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_11 m (v 12) ((v 18) * (v 5))).left_comm]

private theorem chunk_13 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 11 ((v 18) * (v 5)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 8 ((v 13) * (v 5)) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 ((v 20) * (v 5)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 8 ((v 1) * (v 18) * (v 5)) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 8 ((v 13) * (v 5)) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 ((v 20) * (v 5)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_11 m (v 3) ((v 18) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_2_11 m (v 2) ((v 18) * (v 5))).left_comm]
  have h2 : X m 1 (v 1) * X m 11 ((v 18) * (v 5)) = X m 11 ((v 18) * (v 5)) * X m 1 (v 1) * X m 8 ((v 1) * (v 18) * (v 5)) := by
    have h := s_1_11 m (v 1) ((v 18) * (v 5))
    rw [show (v 1) * ((v 18) * (v 5)) = ((v 1) * (v 18) * (v 5)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [swap_suffix h2]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_0_11 m (v 0) ((v 18) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [add_suffix m 11 (v 11) ((v 18) * (v 5)),
      show (v 11) + ((v 18) * (v 5)) = ((v 11) + ((v 18) * (v 5))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_8_2 m ((v 1) * (v 18) * (v 5)) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_3 m ((v 1) * (v 18) * (v 5)) (v 3)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_12 m ((v 1) * (v 18) * (v 5)) (v 12)).left_comm]

private theorem chunk_14 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 8 ((v 1) * (v 18) * (v 5)) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 8 ((v 13) * (v 5)) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 ((v 20) * (v 5)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) * (X m 20 (v 20) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 14 ((v 20) * (v 5)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_13 m ((v 1) * (v 18) * (v 5)) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m ((v 1) * (v 18) * (v 5)) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m ((v 1) * (v 18) * (v 5)) ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_18 m ((v 1) * (v 18) * (v 5)) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 ((v 1) * (v 18) * (v 5)) ((v 13) * (v 5)),
      show ((v 1) * (v 18) * (v 5)) + ((v 13) * (v 5)) = (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m ((v 18) * ((v 5) ^ 2)) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_19 m (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m ((v 18) * ((v 5) ^ 2)) (v 20)).left_comm]

private theorem chunk_15 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) * (X m 20 (v 20) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 14 ((v 20) * (v 5)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 8 (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_20 m (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m ((v 18) * ((v 5) ^ 2)) ((v 20) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) ((v 20) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_14 m (v 20) ((v 20) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_14 m (v 19) ((v 20) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_14 m (v 18) ((v 20) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 20) * (v 5))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 (v 14) ((v 20) * (v 5)),
      show (v 14) + ((v 20) * (v 5)) = ((v 14) + ((v 20) * (v 5))) by abel]

private theorem chunk_16 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 8 (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 19) * (v 4))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m ((v 18) * ((v 5) ^ 2)) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_21 m (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m ((v 18) * ((v 5) ^ 2)) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m ((v 18) * ((v 5) ^ 2)) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_7 m (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m ((v 18) * ((v 5) ^ 2)) ((v 8) + ((v 19) * (v 4)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) ((v 8) + ((v 19) * (v 4))),
      show (((v 13) * (v 5)) + ((v 1) * (v 18) * (v 5))) + ((v 8) + ((v 19) * (v 4))) = ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) by abel]

private theorem chunk_17 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 18) * ((v 5) ^ 2)) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 16 (v 16) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 15 ((v 16) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 ((v 18) * ((v 5) ^ 2)) ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))),
      show ((v 18) * ((v 5) ^ 2)) + ((v 9) + ((v 12) * (v 4)) + ((v 0) * (v 4) * ((v 19) ^ 2))) = ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_16 m ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_16 m ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_16 m (v 7) (v 16)).left_comm]
  have h4 : X m 6 (v 6) * X m 16 (v 16) = X m 16 (v 16) * X m 6 (v 6) * X m 15 ((v 16) * (v 6)) := by
    have h := s_6_16 m (v 6) (v 16)
    rw [show (v 6) * (v 16) = ((v 16) * (v 6)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_16 m (v 21) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_16 m (v 20) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_16 m (v 19) (v 16)).left_comm]

private theorem chunk_18 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 16 (v 16) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 15 ((v 16) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))) =
      X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 16 (v 16) * (X m 1 (v 1) * (X m 14 ((v 1) * (v 16)) * (X m 10 ((v 16) * ((v 1) ^ 2)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 9 ((v 16) * (v 3)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 15 ((v 16) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_16 m (v 18) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_16 m ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_16 m ((v 14) + ((v 20) * (v 5))) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_16 m (v 13) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_16 m (v 12) (v 16)).left_comm]
  have h5 : X m 3 (v 3) * X m 16 (v 16) = X m 16 (v 16) * X m 3 (v 3) * X m 9 ((v 16) * (v 3)) := by
    have h := s_3_16 m (v 3) (v 16)
    rw [show (v 3) * (v 16) = ((v 16) * (v 3)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h5]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_2_16 m (v 2) (v 16)).left_comm]
  have h7 : X m 1 (v 1) * X m 16 (v 16) = X m 16 (v 16) * X m 1 (v 1) * X m 14 ((v 1) * (v 16)) * X m 10 ((v 16) * ((v 1) ^ 2)) := by
    have h := s_1_16 m (v 1) (v 16)
    rw [show (v 1) * (v 16) = ((v 1) * (v 16)) by ring, show (v 16) * (v 1) ^ 2 = ((v 16) * ((v 1) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [swap_suffix_two h7]

private theorem chunk_19 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (v 16) * (X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 16 (v 16) * (X m 1 (v 1) * (X m 14 ((v 1) * (v 16)) * (X m 10 ((v 16) * ((v 1) ^ 2)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 9 ((v 16) * (v 3)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 15 ((v 16) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) =
      X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 10 ((v 16) * ((v 1) ^ 2)) * (X m 0 (v 0) * (X m 9 ((v 0) * (v 16) * ((v 1) ^ 2)) * (X m 1 (v 1) * (X m 14 ((v 1) * (v 16)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 9 ((v 16) * (v 3)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 15 ((v 16) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_0_16 m (v 0) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_11_16 m ((v 11) + ((v 18) * (v 5))) (v 16)).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [(c_10_16 m ((v 10) + ((v 4) * ((v 19) ^ 2))) (v 16)).left_comm]
  conv_lhs =>
    enter [2]
    rw [(c_17_16 m (v 17) (v 16)).left_comm]
  conv_lhs =>
    rw [add_suffix m 16 (v 16) (v 16),
      show (v 16) + (v 16) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_14_10 m ((v 1) * (v 16)) ((v 16) * ((v 1) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_1_10 m (v 1) ((v 16) * ((v 1) ^ 2))).left_comm]
  have h7 : X m 0 (v 0) * X m 10 ((v 16) * ((v 1) ^ 2)) = X m 10 ((v 16) * ((v 1) ^ 2)) * X m 0 (v 0) * X m 9 ((v 0) * (v 16) * ((v 1) ^ 2)) := by
    have h := s_0_10 m (v 0) ((v 16) * ((v 1) ^ 2))
    rw [show (v 0) * ((v 16) * ((v 1) ^ 2)) = ((v 0) * (v 16) * ((v 1) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2]
    rw [swap_suffix h7]

private theorem chunk_20 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 17 (v 17) * (X m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 10 ((v 16) * ((v 1) ^ 2)) * (X m 0 (v 0) * (X m 9 ((v 0) * (v 16) * ((v 1) ^ 2)) * (X m 1 (v 1) * (X m 14 ((v 1) * (v 16)) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 9 ((v 16) * (v 3)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 15 ((v 16) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))))) =
      X m 17 (v 17) * (X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 14 ((v 1) * (v 16)) * (X m 9 ((v 0) * (v 16) * ((v 1) ^ 2)) * (X m 9 ((v 16) * (v 3)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 15 ((v 16) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2]
    rw [(c_11_10 m ((v 11) + ((v 18) * (v 5))) ((v 16) * ((v 1) ^ 2))).left_comm]
  conv_lhs =>
    enter [2]
    rw [add_suffix m 10 ((v 10) + ((v 4) * ((v 19) ^ 2))) ((v 16) * ((v 1) ^ 2)),
      show ((v 10) + ((v 4) * ((v 19) ^ 2))) + ((v 16) * ((v 1) ^ 2)) = ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_9_1 m ((v 0) * (v 16) * ((v 1) ^ 2)) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_9_14 m ((v 0) * (v 16) * ((v 1) ^ 2)) ((v 1) * (v 16))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_9_2 m ((v 0) * (v 16) * ((v 1) ^ 2)) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_14_2 m ((v 1) * (v 16)) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_3 m ((v 0) * (v 16) * ((v 1) ^ 2)) (v 3)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_14_3 m ((v 1) * (v 16)) (v 3)).left_comm]

private theorem chunk_21 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 17 (v 17) * (X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 14 ((v 1) * (v 16)) * (X m 9 ((v 0) * (v 16) * ((v 1) ^ 2)) * (X m 9 ((v 16) * (v 3)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 15 ((v 16) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))) =
      X m 17 (v 17) * (X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 9 (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 15 ((v 16) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 ((v 0) * (v 16) * ((v 1) ^ 2)) ((v 16) * (v 3)),
      show ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 16) * (v 3)) = (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_12 m (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) (v 12)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_12 m ((v 1) * (v 16)) (v 12)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_13 m ((v 1) * (v 16)) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) ((v 14) + ((v 20) * (v 5)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 ((v 1) * (v 16)) ((v 14) + ((v 20) * (v 5))),
      show ((v 1) * (v 16)) + ((v 14) + ((v 20) * (v 5))) = ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2)))).left_comm]

private theorem chunk_22 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 17 (v 17) * (X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 9 (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 15 ((v 16) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) =
      X m 17 (v 17) * (X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 15 ((v 16) * (v 6)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 9 (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) ((v 16) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_15 m (v 6) ((v 16) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_15 m (v 21) ((v 16) * (v 6))).left_comm]

private theorem chunk_23 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 17 (v 17) * (X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 15 ((v 16) * (v 6)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 9 (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) =
      X m 17 (v 17) * (X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 17 (v 17) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_15 m (v 20) ((v 16) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_15 m (v 19) ((v 16) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m (v 18) ((v 16) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 16) * (v 6)),
      show ((v 15) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) + ((v 16) * (v 6)) = ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))),
      show (((v 16) * (v 3)) + ((v 0) * (v 16) * ((v 1) ^ 2))) + ((v 9) + ((v 12) * (v 4)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) = ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_17 m ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) (v 17)).left_comm]

private theorem chunk_24 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 17 (v 17) * (X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 17 (v 17) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 17 (v 17) * (X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 17 (v 17) * (X m 15 ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 14 ((v 17) * (v 7)) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_17 m ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) (v 17)).left_comm]
  have h1 : X m 7 (v 7) * X m 17 (v 17) = X m 17 (v 17) * X m 7 (v 7) * X m 14 ((v 17) * (v 7)) := by
    have h := s_7_17 m (v 7) (v 17)
    rw [show (v 7) * (v 17) = ((v 17) * (v 7)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h1]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_17 m (v 6) (v 17)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_17 m (v 21) (v 17)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_17 m (v 20) (v 17)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_17 m (v 19) (v 17)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_17 m (v 18) (v 17)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_17 m ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) (v 17)).left_comm]

private theorem chunk_25 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 17 (v 17) * (X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 17 (v 17) * (X m 15 ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 14 ((v 17) * (v 7)) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) =
      X m 17 (v 17) * (X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 11 ((v 0) * (v 17)) * (X m 15 ((v 0) * ((v 17) ^ 2)) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 8 ((v 17) * (v 2)) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 14 ((v 17) * (v 7)) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_17 m ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) (v 17)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_17 m (v 13) (v 17)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_17 m (v 12) (v 17)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_3_17 m (v 3) (v 17)).left_comm]
  have h4 : X m 2 (v 2) * X m 17 (v 17) = X m 17 (v 17) * X m 2 (v 2) * X m 8 ((v 17) * (v 2)) := by
    have h := s_2_17 m (v 2) (v 17)
    rw [show (v 2) * (v 17) = ((v 17) * (v 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_1_17 m (v 1) (v 17)).left_comm]
  have h6 : X m 0 (v 0) * X m 17 (v 17) = X m 17 (v 17) * X m 0 (v 0) * X m 11 ((v 0) * (v 17)) * X m 15 ((v 0) * ((v 17) ^ 2)) := by
    have h := s_0_17 m (v 0) (v 17)
    rw [show (v 0) * (v 17) = ((v 0) * (v 17)) by ring, show (v 0) * (v 17) ^ 2 = ((v 0) * ((v 17) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2]
    rw [swap_suffix_two h6]
  conv_lhs =>
    enter [2, 2]
    rw [(c_11_17 m ((v 11) + ((v 18) * (v 5))) (v 17)).left_comm]

private theorem chunk_26 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 17 (v 17) * (X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 17 (v 17) * (X m 11 ((v 11) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 11 ((v 0) * (v 17)) * (X m 15 ((v 0) * ((v 17) ^ 2)) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 8 ((v 17) * (v 2)) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 14 ((v 17) * (v 7)) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))) =
      X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 15 ((v 0) * ((v 17) ^ 2)) * (X m 8 ((v 17) * (v 2)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 14 ((v 17) * (v 7)) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2]
    rw [(c_10_17 m ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) (v 17)).left_comm]
  conv_lhs =>
    rw [add_suffix m 17 (v 17) (v 17),
      show (v 17) + (v 17) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2]
    rw [(c_0_11 m (v 0) ((v 0) * (v 17))).left_comm]
  conv_lhs =>
    enter [2]
    rw [add_suffix m 11 ((v 11) + ((v 18) * (v 5))) ((v 0) * (v 17)),
      show ((v 11) + ((v 18) * (v 5))) + ((v 0) * (v 17)) = ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) by abel]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_15_1 m ((v 0) * ((v 17) ^ 2)) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_15_2 m ((v 0) * ((v 17) ^ 2)) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_8_3 m ((v 17) * (v 2)) (v 3)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_15_3 m ((v 0) * ((v 17) ^ 2)) (v 3)).left_comm]

private theorem chunk_27 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 15 ((v 0) * ((v 17) ^ 2)) * (X m 8 ((v 17) * (v 2)) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 14 ((v 17) * (v 7)) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) =
      X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 8 ((v 17) * (v 2)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 14 ((v 17) * (v 7)) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_12 m ((v 17) * (v 2)) (v 12)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_15_12 m ((v 0) * ((v 17) ^ 2)) (v 12)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_13 m ((v 17) * (v 2)) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_13 m ((v 0) * ((v 17) ^ 2)) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m ((v 17) * (v 2)) ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m ((v 0) * ((v 17) ^ 2)) ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m ((v 17) * (v 2)) ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 0) * ((v 17) ^ 2)) ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))),
      show ((v 0) * ((v 17) ^ 2)) + ((v 15) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) = ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) by abel]

private theorem chunk_28 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 8 ((v 17) * (v 2)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 14 ((v 17) * (v 7)) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 14 ((v 17) * (v 7)) * (X m 7 (v 7) * (X m 8 ((v 17) * (v 2)) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_18 m ((v 17) * (v 2)) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_19 m ((v 17) * (v 2)) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_20 m ((v 17) * (v 2)) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_21 m ((v 17) * (v 2)) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m ((v 17) * (v 2)) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_7 m ((v 17) * (v 2)) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m ((v 17) * (v 2)) ((v 17) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_14 m (v 7) ((v 17) * (v 7))).left_comm]

private theorem chunk_29 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 14 ((v 17) * (v 7)) * (X m 7 (v 7) * (X m 8 ((v 17) * (v 2)) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_14 m (v 6) ((v 17) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_14 m (v 21) ((v 17) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_14 m (v 20) ((v 17) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_14 m (v 19) ((v 17) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_14 m (v 18) ((v 17) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 17) * (v 7))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) ((v 17) * (v 7)),
      show ((v 14) + ((v 1) * (v 16)) + ((v 20) * (v 5))) + ((v 17) * (v 7)) = ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 ((v 17) * (v 2)) ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))),
      show ((v 17) * (v 2)) + ((v 8) + ((v 13) * (v 5)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) = ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) by abel]

private theorem chunk_30 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) =
      X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 18 (v 18) * (X m 15 ((v 10) * (v 18)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_10 m ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) (v 10)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_10 m ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) (v 10)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_10 m (v 7) (v 10)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_10 m (v 6) (v 10)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_10 m (v 21) (v 10)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_10 m (v 20) (v 10)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_10 m (v 19) (v 10)).left_comm]
  have h7 : X m 18 (v 18) * X m 10 (v 10) = X m 10 (v 10) * X m 18 (v 18) * X m 15 ((v 10) * (v 18)) := by
    have h := s_18_10 m (v 18) (v 10)
    rw [show (v 18) * (v 10) = ((v 10) * (v 18)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h7]

private theorem chunk_31 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 10 (v 10) * (X m 18 (v 18) * (X m 15 ((v 10) * (v 18)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) =
      X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 10 (v 10) * (X m 0 (v 0) * (X m 9 ((v 0) * (v 10)) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 15 ((v 10) * (v 18)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_10 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) (v 10)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_10 m ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) (v 10)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_10 m (v 13) (v 10)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_12_10 m (v 12) (v 10)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_3_10 m (v 3) (v 10)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_2_10 m (v 2) (v 10)).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_1_10 m (v 1) (v 10)).left_comm]
  have h7 : X m 0 (v 0) * X m 10 (v 10) = X m 10 (v 10) * X m 0 (v 0) * X m 9 ((v 0) * (v 10)) := by
    have h := s_0_10 m (v 0) (v 10)
    rw [show (v 0) * (v 10) = ((v 0) * (v 10)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2]
    rw [swap_suffix h7]

private theorem chunk_32 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 10 (v 10) * (X m 0 (v 0) * (X m 9 ((v 0) * (v 10)) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 15 ((v 10) * (v 18)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 9 ((v 0) * (v 10)) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 15 ((v 10) * (v 18)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2]
    rw [(c_11_10 m ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) (v 10)).left_comm]
  conv_lhs =>
    rw [add_suffix m 10 ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) (v 10),
      show ((v 10) + ((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) + (v 10) = (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_9_1 m ((v 0) * (v 10)) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_9_2 m ((v 0) * (v 10)) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_9_3 m ((v 0) * (v 10)) (v 3)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_9_12 m ((v 0) * (v 10)) (v 12)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m ((v 0) * (v 10)) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m ((v 0) * (v 10)) ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5)))).left_comm]

private theorem chunk_33 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 9 ((v 0) * (v 10)) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 15 ((v 10) * (v 18)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) =
      X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 9 ((v 0) * (v 10)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m ((v 0) * (v 10)) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m ((v 0) * (v 10)) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m ((v 0) * (v 10)) ((v 10) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m (v 18) ((v 10) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 10) * (v 18)),
      show ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) + ((v 10) * (v 18)) = ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m ((v 0) * (v 10)) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m ((v 0) * (v 10)) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m ((v 0) * (v 10)) (v 21)).left_comm]

private theorem chunk_34 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 9 ((v 0) * (v 10)) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) =
      X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 11 (v 11) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m ((v 0) * (v 10)) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m ((v 0) * (v 10)) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m ((v 0) * (v 10)) ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 ((v 0) * (v 10)) ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))),
      show ((v 0) * (v 10)) + ((v 9) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) = ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_11 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) (v 11)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_11 m ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) (v 11)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_11 m (v 7) (v 11)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_11 m (v 6) (v 11)).left_comm]

private theorem chunk_35 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 11 (v 11) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) =
      X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 ((v 11) * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_11 m (v 21) (v 11)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_11 m (v 20) (v 11)).left_comm]
  have h2 : X m 19 (v 19) * X m 11 (v 11) = X m 11 (v 11) * X m 19 (v 19) * X m 14 ((v 11) * (v 19)) := by
    have h := s_19_11 m (v 19) (v 11)
    rw [show (v 19) * (v 11) = ((v 11) * (v 19)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h2]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_11 m (v 18) (v 11)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_11 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) (v 11)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_11 m ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) (v 11)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_11 m (v 13) (v 11)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_12_11 m (v 12) (v 11)).left_comm]

private theorem chunk_36 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 11 (v 11) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 ((v 11) * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) =
      X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 8 ((v 1) * (v 11)) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 ((v 11) * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_3_11 m (v 3) (v 11)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_2_11 m (v 2) (v 11)).left_comm]
  have h2 : X m 1 (v 1) * X m 11 (v 11) = X m 11 (v 11) * X m 1 (v 1) * X m 8 ((v 1) * (v 11)) := by
    have h := s_1_11 m (v 1) (v 11)
    rw [show (v 1) * (v 11) = ((v 1) * (v 11)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2]
    rw [swap_suffix h2]
  conv_lhs =>
    enter [2, 2]
    rw [(c_0_11 m (v 0) (v 11)).left_comm]
  conv_lhs =>
    enter [2]
    rw [add_suffix m 11 ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) (v 11),
      show ((v 11) + ((v 0) * (v 17)) + ((v 18) * (v 5))) + (v 11) = (((v 0) * (v 17)) + ((v 18) * (v 5))) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_8_2 m ((v 1) * (v 11)) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_8_3 m ((v 1) * (v 11)) (v 3)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_8_12 m ((v 1) * (v 11)) (v 12)).left_comm]

private theorem chunk_37 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 8 ((v 1) * (v 11)) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 ((v 11) * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) =
      X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 14 ((v 11) * (v 19)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 1) * (v 11)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_13 m ((v 1) * (v 11)) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m ((v 1) * (v 11)) ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m ((v 1) * (v 11)) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_18 m ((v 1) * (v 11)) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_19 m ((v 1) * (v 11)) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m ((v 1) * (v 11)) ((v 11) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_14 m (v 19) ((v 11) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_14 m (v 18) ((v 11) * (v 19))).left_comm]

private theorem chunk_38 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 14 ((v 11) * (v 19)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 1) * (v 11)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) =
      X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 0 (v 0) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 11) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) ((v 11) * (v 19)),
      show ((v 14) + ((v 1) * (v 16)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) + ((v 11) * (v 19)) = ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_20 m ((v 1) * (v 11)) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_21 m ((v 1) * (v 11)) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m ((v 1) * (v 11)) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_7 m ((v 1) * (v 11)) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 ((v 1) * (v 11)) ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))),
      show ((v 1) * (v 11)) + ((v 8) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) = ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_0 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) (v 0)).left_comm]

private theorem chunk_39 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 0 (v 0) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))) =
      X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 0 (v 0) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 7 ((v 0) * (v 19)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_0 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) (v 0)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_0 m (v 7) (v 0)).left_comm]
  have h2 : X m 6 (v 6) * X m 0 (v 0) = X m 0 (v 0) * X m 6 (v 6) * X m 4 ((v 0) * (v 6)) := by
    have h := s_6_0 m (v 6) (v 0)
    rw [show (v 6) * (v 0) = ((v 0) * (v 6)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h2]
  have h3 : X m 21 (v 21) * X m 0 (v 0) = X m 0 (v 0) * X m 21 (v 21) * X m 16 ((v 0) * (v 21)) := by
    have h := s_21_0 m (v 21) (v 0)
    rw [show (v 21) * (v 0) = ((v 0) * (v 21)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h3]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_0 m (v 20) (v 0)).left_comm]
  have h5 : X m 19 (v 19) * X m 0 (v 0) = X m 0 (v 0) * X m 19 (v 19) * X m 7 ((v 0) * (v 19)) * X m 12 ((v 0) * ((v 19) ^ 2)) := by
    have h := s_19_0 m (v 19) (v 0)
    rw [show (v 19) * (v 0) = ((v 0) * (v 19)) by ring, show (v 0) * (v 19) ^ 2 = ((v 0) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h5]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_0 m (v 18) (v 0)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_0 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) (v 0)).left_comm]

private theorem chunk_40 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 0 (v 0) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 7 ((v 0) * (v 19)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 0) * (v 1)) * (X m 2 (v 2) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 7 ((v 0) * (v 19)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_0 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) (v 0)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_0 m (v 13) (v 0)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_12_0 m (v 12) (v 0)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_3_0 m (v 3) (v 0)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_2_0 m (v 2) (v 0)).left_comm]
  have h5 : X m 1 (v 1) * X m 0 (v 0) = X m 0 (v 0) * X m 1 (v 1) * X m 2 ((v 0) * (v 1)) * X m 3 ((v 0) * ((v 1) ^ 2)) := by
    have h := s_1_0 m (v 1) (v 0)
    rw [show (v 1) * (v 0) = ((v 0) * (v 1)) by ring, show (v 0) * (v 1) ^ 2 = ((v 0) * ((v 1) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2]
    rw [swap_suffix_two h5]
  conv_lhs =>
    enter [2, 2]
    rw [add_suffix m 0 (v 0) (v 0),
      show (v 0) + (v 0) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_3_2 m ((v 0) * ((v 1) ^ 2)) (v 2)).left_comm]

private theorem chunk_41 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 0) * (v 1)) * (X m 2 (v 2) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 7 ((v 0) * (v 19)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 (v 12) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 (v 13) * (X m 14 ((v 0) * (v 13) * ((v 19) ^ 2)) * (X m 15 ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 19 (v 19) * (X m 7 ((v 0) * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2]
    rw [add_suffix m 2 ((v 0) * (v 1)) (v 2),
      show ((v 0) * (v 1)) + (v 2) = ((v 2) + ((v 0) * (v 1))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [add_suffix m 3 ((v 0) * ((v 1) ^ 2)) (v 3),
      show ((v 0) * ((v 1) ^ 2)) + (v 3) = ((v 3) + ((v 0) * ((v 1) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_12 m ((v 0) * (v 19)) ((v 0) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_12 m (v 19) ((v 0) * ((v 19) ^ 2))).left_comm]
  have h4 : X m 18 (v 18) * X m 12 ((v 0) * ((v 19) ^ 2)) = X m 12 ((v 0) * ((v 19) ^ 2)) * X m 18 (v 18) * X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) := by
    have h := s_18_12 m (v 18) ((v 0) * ((v 19) ^ 2))
    rw [show (v 18) * ((v 0) * ((v 19) ^ 2)) = ((v 0) * (v 18) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_12 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 0) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_12 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) ((v 0) * ((v 19) ^ 2))).left_comm]
  have h7 : X m 13 (v 13) * X m 12 ((v 0) * ((v 19) ^ 2)) = X m 12 ((v 0) * ((v 19) ^ 2)) * X m 13 (v 13) * X m 14 ((v 0) * (v 13) * ((v 19) ^ 2)) * X m 15 ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) := by
    have h := s_13_12 m (v 13) ((v 0) * ((v 19) ^ 2))
    rw [show (v 13) * ((v 0) * ((v 19) ^ 2)) = ((v 0) * (v 13) * ((v 19) ^ 2)) by ring, show ((v 0) * ((v 19) ^ 2)) * (v 13) ^ 2 = ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h7]

private theorem chunk_42 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 (v 12) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 (v 13) * (X m 14 ((v 0) * (v 13) * ((v 19) ^ 2)) * (X m 15 ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 19 (v 19) * (X m 7 ((v 0) * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) =
      X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 7 ((v 0) * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [add_suffix m 12 (v 12) ((v 0) * ((v 19) ^ 2)),
      show (v 12) + ((v 0) * ((v 19) ^ 2)) = ((v 12) + ((v 0) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 ((v 0) * (v 13) * ((v 19) ^ 2)) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))),
      show ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5))) = ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))),
      show ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 18) * (v 4) * ((v 19) ^ 2))) = ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_16 m (v 18) ((v 0) * (v 18) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_16 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 0) * (v 18) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_16 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2))) ((v 0) * (v 18) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_13_16 m (v 13) ((v 0) * (v 18) * ((v 19) ^ 2))).left_comm]

private theorem chunk_43 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 7 ((v 0) * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) =
      X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 10 ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2)) * (X m 1 (v 1) * (X m 14 ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 7 ((v 0) * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_12_16 m ((v 12) + ((v 0) * ((v 19) ^ 2))) ((v 0) * (v 18) * ((v 19) ^ 2))).left_comm]
  have h1 : X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) = X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) := by
    have h := s_3_16 m ((v 3) + ((v 0) * ((v 1) ^ 2))) ((v 0) * (v 18) * ((v 19) ^ 2))
    rw [show ((v 3) + ((v 0) * ((v 1) ^ 2))) * ((v 0) * (v 18) * ((v 19) ^ 2)) = (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [swap_suffix h1]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_2_16 m ((v 2) + ((v 0) * (v 1))) ((v 0) * (v 18) * ((v 19) ^ 2))).left_comm]
  have h3 : X m 1 (v 1) * X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) = X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * X m 1 (v 1) * X m 14 ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) * X m 10 ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2)) := by
    have h := s_1_16 m (v 1) ((v 0) * (v 18) * ((v 19) ^ 2))
    rw [show (v 1) * ((v 0) * (v 18) * ((v 19) ^ 2)) = ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) by ring, show ((v 0) * (v 18) * ((v 19) ^ 2)) * (v 1) ^ 2 = ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2]
    rw [swap_suffix_two h3]
  conv_lhs =>
    enter [2]
    rw [(c_11_16 m (((v 0) * (v 17)) + ((v 18) * (v 5))) ((v 0) * (v 18) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    rw [(c_10_16 m (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) ((v 0) * (v 18) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_14_10 m ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_1_10 m (v 1) ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))).left_comm]

private theorem chunk_44 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 10 ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2)) * (X m 1 (v 1) * (X m 14 ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 7 ((v 0) * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) =
      X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 7 ((v 0) * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2]
    rw [(c_11_10 m (((v 0) * (v 17)) + ((v 18) * (v 5))) ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2]
    rw [add_suffix m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2)),
      show (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2))) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2)) = (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_14_2 m ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) ((v 2) + ((v 0) * (v 1)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_14_3 m ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) ((v 3) + ((v 0) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_12 m (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 12) + ((v 0) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_14_12 m ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) ((v 12) + ((v 0) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_13 m ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) (v 13)).left_comm]

private theorem chunk_45 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 7 ((v 0) * (v 19)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 7 ((v 0) * (v 19)) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2))),
      show ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2))) = ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 0) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_20 m ((v 0) * (v 19)) (v 20)).left_comm]

private theorem chunk_46 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 7 ((v 0) * (v 19)) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 21 (v 21) * (X m 16 ((v 0) * (v 21)) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) =
      X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 16 ((v 0) * (v 21)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 7 ((v 0) * (v 19)) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_21 m ((v 0) * (v 19)) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_16 m (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 0) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_16 m ((v 0) * (v 19)) ((v 0) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_16 m (v 21) ((v 0) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_16 m (v 20) ((v 0) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_16 m (v 19) ((v 0) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_16 m (v 18) ((v 0) * (v 21))).left_comm]

private theorem chunk_47 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 16 ((v 0) * (v 21)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 7 ((v 0) * (v 19)) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) =
      X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 16 ((v 0) * (v 21)) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 14 ((v 0) * (v 1) * (v 21)) * (X m 10 ((v 0) * (v 21) * ((v 1) ^ 2)) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 7 ((v 0) * (v 19)) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_16 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 0) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_16 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) ((v 0) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_16 m (v 13) ((v 0) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_12_16 m ((v 12) + ((v 0) * ((v 19) ^ 2))) ((v 0) * (v 21))).left_comm]
  have h4 : X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * X m 16 ((v 0) * (v 21)) = X m 16 ((v 0) * (v 21)) * X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) := by
    have h := s_3_16 m ((v 3) + ((v 0) * ((v 1) ^ 2))) ((v 0) * (v 21))
    rw [show ((v 3) + ((v 0) * ((v 1) ^ 2))) * ((v 0) * (v 21)) = (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_2_16 m ((v 2) + ((v 0) * (v 1))) ((v 0) * (v 21))).left_comm]
  have h6 : X m 1 (v 1) * X m 16 ((v 0) * (v 21)) = X m 16 ((v 0) * (v 21)) * X m 1 (v 1) * X m 14 ((v 0) * (v 1) * (v 21)) * X m 10 ((v 0) * (v 21) * ((v 1) ^ 2)) := by
    have h := s_1_16 m (v 1) ((v 0) * (v 21))
    rw [show (v 1) * ((v 0) * (v 21)) = ((v 0) * (v 1) * (v 21)) by ring, show ((v 0) * (v 21)) * (v 1) ^ 2 = ((v 0) * (v 21) * ((v 1) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2]
    rw [swap_suffix_two h6]
  conv_lhs =>
    enter [2, 2]
    rw [(c_11_16 m (((v 0) * (v 17)) + ((v 18) * (v 5))) ((v 0) * (v 21))).left_comm]

private theorem chunk_48 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 16 ((v 0) * (v 21)) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 14 ((v 0) * (v 1) * (v 21)) * (X m 10 ((v 0) * (v 21) * ((v 1) ^ 2)) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 7 ((v 0) * (v 19)) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) =
      X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 14 ((v 0) * (v 1) * (v 21)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 7 ((v 0) * (v 19)) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2]
    rw [(c_10_16 m (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 0) * (v 21))).left_comm]
  conv_lhs =>
    rw [add_suffix m 16 ((v 0) * (v 18) * ((v 19) ^ 2)) ((v 0) * (v 21)),
      show ((v 0) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 21)) = (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_14_10 m ((v 0) * (v 1) * (v 21)) ((v 0) * (v 21) * ((v 1) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_1_10 m (v 1) ((v 0) * (v 21) * ((v 1) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [(c_11_10 m (((v 0) * (v 17)) + ((v 18) * (v 5))) ((v 0) * (v 21) * ((v 1) ^ 2))).left_comm]
  conv_lhs =>
    enter [2]
    rw [add_suffix m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 0) * (v 21) * ((v 1) ^ 2)),
      show (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) + ((v 0) * (v 21) * ((v 1) ^ 2)) = (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_14_2 m ((v 0) * (v 1) * (v 21)) ((v 2) + ((v 0) * (v 1)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_14_3 m ((v 0) * (v 1) * (v 21)) ((v 3) + ((v 0) * ((v 1) ^ 2)))).left_comm]

private theorem chunk_49 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 14 ((v 0) * (v 1) * (v 21)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 7 ((v 0) * (v 19)) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 7 ((v 0) * (v 19)) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_12 m (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) ((v 12) + ((v 0) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_14_12 m ((v 0) * (v 1) * (v 21)) ((v 12) + ((v 0) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_13 m ((v 0) * (v 1) * (v 21)) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 ((v 0) * (v 1) * (v 21)) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))),
      show ((v 0) * (v 1) * (v 21)) + ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) = ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) (v 18)).left_comm]

private theorem chunk_50 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 7 ((v 0) * (v 19)) * (X m 9 (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 6 (v 6) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) =
      X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) ((v 0) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))),
      show (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) + (((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) = (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (v 6)).left_comm]
  have h6 : X m 7 ((v 0) * (v 19)) * X m 6 (v 6) = X m 6 (v 6) * X m 7 ((v 0) * (v 19)) * X m 8 ((v 0) * (v 19) * (v 6)) * X m 9 ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) := by
    have h := s_7_6 m ((v 0) * (v 19)) (v 6)
    rw [show ((v 0) * (v 19)) * (v 6) = ((v 0) * (v 19) * (v 6)) by ring, show (v 6) * ((v 0) * (v 19)) ^ 2 = ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h6]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))),
      show ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) = (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) by abel]

private theorem chunk_51 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 4 ((v 0) * (v 6)) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) =
      X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 4 ((v 0) * (v 6)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 10 ((v 0) * (v 6) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 0) * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_4 m (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 0) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_4 m ((v 0) * (v 19) * (v 6)) ((v 0) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_4 m ((v 0) * (v 19)) ((v 0) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_4 m (v 6) ((v 0) * (v 6))).left_comm]
  have h4 : X m 21 (v 21) * X m 4 ((v 0) * (v 6)) = X m 4 ((v 0) * (v 6)) * X m 21 (v 21) * X m 15 ((v 0) * (v 21) * (v 6)) := by
    have h := s_21_4 m (v 21) ((v 0) * (v 6))
    rw [show (v 21) * ((v 0) * (v 6)) = ((v 0) * (v 21) * (v 6)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_4 m (v 20) ((v 0) * (v 6))).left_comm]
  have h6 : X m 19 (v 19) * X m 4 ((v 0) * (v 6)) = X m 4 ((v 0) * (v 6)) * X m 19 (v 19) * X m 8 ((v 0) * (v 19) * (v 6)) * X m 10 ((v 0) * (v 6) * ((v 19) ^ 2)) := by
    have h := s_19_4 m (v 19) ((v 0) * (v 6))
    rw [show (v 19) * ((v 0) * (v 6)) = ((v 0) * (v 19) * (v 6)) by ring, show ((v 0) * (v 6)) * (v 19) ^ 2 = ((v 0) * (v 6) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h6]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_4 m (v 18) ((v 0) * (v 6))).left_comm]

private theorem chunk_52 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 4 ((v 0) * (v 6)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 10 ((v 0) * (v 6) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 0) * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) =
      X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 4 ((v 0) * (v 6)) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 10 ((v 0) * (v 6) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 0) * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_4 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 0) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_4 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) ((v 0) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_4 m (v 13) ((v 0) * (v 6))).left_comm]
  have h3 : X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * X m 4 ((v 0) * (v 6)) = X m 4 ((v 0) * (v 6)) * X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) := by
    have h := s_12_4 m ((v 12) + ((v 0) * ((v 19) ^ 2))) ((v 0) * (v 6))
    rw [show ((v 12) + ((v 0) * ((v 19) ^ 2))) * ((v 0) * (v 6)) = (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [swap_suffix h3]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_3_4 m ((v 3) + ((v 0) * ((v 1) ^ 2))) ((v 0) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_2_4 m ((v 2) + ((v 0) * (v 1))) ((v 0) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_1_4 m (v 1) ((v 0) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [(c_11_4 m (((v 0) * (v 17)) + ((v 18) * (v 5))) ((v 0) * (v 6))).left_comm]

private theorem chunk_53 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 4 ((v 0) * (v 6)) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 10 ((v 0) * (v 6) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 0) * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) * (X m 10 ((v 0) * (v 6) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 0) * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2]
    rw [(c_10_4 m (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 0) * (v 6))).left_comm]
  conv_lhs =>
    rw [(c_16_4 m (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) ((v 0) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) ((v 0) * (v 19) * (v 6))).left_comm]

private theorem chunk_54 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) * (X m 10 ((v 0) * (v 6) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 0) * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 10 ((v 0) * (v 6) * ((v 19) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 15 ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2)) * (X m 19 (v 19) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 0) * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_10 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) ((v 0) * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_10 m ((v 0) * (v 19) * (v 6)) ((v 0) * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_10 m (v 19) ((v 0) * (v 6) * ((v 19) ^ 2))).left_comm]
  have h3 : X m 18 (v 18) * X m 10 ((v 0) * (v 6) * ((v 19) ^ 2)) = X m 10 ((v 0) * (v 6) * ((v 19) ^ 2)) * X m 18 (v 18) * X m 15 ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2)) := by
    have h := s_18_10 m (v 18) ((v 0) * (v 6) * ((v 19) ^ 2))
    rw [show (v 18) * ((v 0) * (v 6) * ((v 19) ^ 2)) = ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h3]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_10 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 0) * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_10 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) ((v 0) * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_10 m (v 13) ((v 0) * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_10 m ((v 12) + ((v 0) * ((v 19) ^ 2))) ((v 0) * (v 6) * ((v 19) ^ 2))).left_comm]

private theorem chunk_55 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 10 ((v 0) * (v 6) * ((v 19) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 15 ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2)) * (X m 19 (v 19) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 15 ((v 0) * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 20 (v 20) * (X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) * (X m 21 (v 21) * (X m 15 ((v 0) * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_3_10 m ((v 3) + ((v 0) * ((v 1) ^ 2))) ((v 0) * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_2_10 m ((v 2) + ((v 0) * (v 1))) ((v 0) * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_1_10 m (v 1) ((v 0) * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_11_10 m (((v 0) * (v 17)) + ((v 18) * (v 5))) ((v 0) * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [add_suffix m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 0) * (v 6) * ((v 19) ^ 2)),
      show (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) + ((v 0) * (v 6) * ((v 19) ^ 2)) = (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m (v 18) ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2)),
      show ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2))) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2)) = ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) (v 20)).left_comm]

private theorem chunk_56 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 20 (v 20) * (X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) * (X m 21 (v 21) * (X m 15 ((v 0) * (v 21) * (v 6)) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 15 ((v 0) * (v 21) * (v 6)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_20 m ((v 0) * (v 19) * (v 6)) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_21 m ((v 0) * (v 19) * (v 6)) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) ((v 0) * (v 21) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m ((v 0) * (v 19) * (v 6)) ((v 0) * (v 21) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_15 m (v 21) ((v 0) * (v 21) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_15 m (v 20) ((v 0) * (v 21) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_15 m (v 19) ((v 0) * (v 21) * (v 6))).left_comm]

private theorem chunk_57 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 15 ((v 0) * (v 21) * (v 6)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 0) * (v 19) * (v 6)) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m (v 18) ((v 0) * (v 21) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 0) * (v 21) * (v 6)),
      show ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) + ((v 0) * (v 21) * (v 6)) = ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m ((v 0) * (v 19) * (v 6)) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) ((v 0) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_7 m ((v 0) * (v 19) * (v 6)) ((v 0) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) ((v 0) * (v 19) * (v 6))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 ((v 0) * (v 19) * (v 6)) ((v 0) * (v 19) * (v 6)),
      show ((v 0) * (v 19) * (v 6)) + ((v 0) * (v 19) * (v 6)) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]

private theorem chunk_58 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 0) * (v 19)) * (X m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) * (X m 9 (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 (v 7) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 1 (v 1) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))),
      show (((v 0) * (v 12) * (v 6)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) + (((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) = (((v 0) * (v 12) * (v 6)) + ((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m (((v 0) * (v 12) * (v 6)) + ((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 7 ((v 0) * (v 19)) (v 7),
      show ((v 0) * (v 19)) + (v 7) = ((v 7) + ((v 0) * (v 19))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (((v 0) * (v 12) * (v 6)) + ((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 (((v 0) * (v 12) * (v 6)) + ((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))),
      show (((v 0) * (v 12) * (v 6)) + ((v 0) * (v 21) * (v 3)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) + ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 4) * ((v 19) ^ 2))) = ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_1 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_1 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) (v 1)).left_comm]
  have h7 : X m 7 ((v 7) + ((v 0) * (v 19))) * X m 1 (v 1) = X m 1 (v 1) * X m 7 ((v 7) + ((v 0) * (v 19))) * X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) := by
    have h := s_7_1 m ((v 7) + ((v 0) * (v 19))) (v 1)
    rw [show ((v 7) + ((v 0) * (v 19))) * (v 1) = (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h7]

private theorem chunk_59 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 1 (v 1) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 13 ((v 1) * (v 18)) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 17 ((v 1) * (v 20)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_1 m (v 6) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_1 m (v 21) (v 1)).left_comm]
  have h2 : X m 20 (v 20) * X m 1 (v 1) = X m 1 (v 1) * X m 20 (v 20) * X m 17 ((v 1) * (v 20)) := by
    have h := s_20_1 m (v 20) (v 1)
    rw [show (v 20) * (v 1) = ((v 1) * (v 20)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h2]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_1 m (v 19) (v 1)).left_comm]
  have h4 : X m 18 (v 18) * X m 1 (v 1) = X m 1 (v 1) * X m 18 (v 18) * X m 13 ((v 1) * (v 18)) * X m 6 ((v 18) * ((v 1) ^ 2)) := by
    have h := s_18_1 m (v 18) (v 1)
    rw [show (v 18) * (v 1) = ((v 1) * (v 18)) by ring, show (v 18) * (v 1) ^ 2 = ((v 18) * ((v 1) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_1 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_1 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_1 m (v 13) (v 1)).left_comm]

private theorem chunk_60 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 1 (v 1) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 1 (v 1) * (X m 13 (v 13) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 13 ((v 1) * (v 18)) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 17 ((v 1) * (v 20)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 17 ((v 1) * (v 20)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_1 m ((v 12) + ((v 0) * ((v 19) ^ 2))) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_3_1 m ((v 3) + ((v 0) * ((v 1) ^ 2))) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_2_1 m ((v 2) + ((v 0) * (v 1))) (v 1)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [add_suffix m 1 (v 1) (v 1),
      show (v 1) + (v 1) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_13 m (v 18) ((v 1) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_13 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 1) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_13 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) ((v 1) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 13 (v 13) ((v 1) * (v 18)),
      show (v 13) + ((v 1) * (v 18)) = ((v 13) + ((v 1) * (v 18))) by abel]

private theorem chunk_61 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 17 ((v 1) * (v 20)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 17 ((v 1) * (v 20)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_19 m ((v 18) * ((v 1) ^ 2)) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_20 m ((v 18) * ((v 1) ^ 2)) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_17 m ((v 18) * ((v 1) ^ 2)) ((v 1) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_17 m (v 20) ((v 1) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_17 m (v 19) ((v 1) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_17 m (v 18) ((v 1) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_17 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 1) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_17 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) ((v 1) * (v 20))).left_comm]

private theorem chunk_62 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 17 ((v 1) * (v 20)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_17 m ((v 13) + ((v 1) * (v 18))) ((v 1) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_12_17 m ((v 12) + ((v 0) * ((v 19) ^ 2))) ((v 1) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_3_17 m ((v 3) + ((v 0) * ((v 1) ^ 2))) ((v 1) * (v 20))).left_comm]
  have h3 : X m 2 ((v 2) + ((v 0) * (v 1))) * X m 17 ((v 1) * (v 20)) = X m 17 ((v 1) * (v 20)) * X m 2 ((v 2) + ((v 0) * (v 1))) * X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) := by
    have h := s_2_17 m ((v 2) + ((v 0) * (v 1))) ((v 1) * (v 20))
    rw [show ((v 2) + ((v 0) * (v 1))) * ((v 1) * (v 20)) = (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [swap_suffix h3]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_11_17 m (((v 0) * (v 17)) + ((v 18) * (v 5))) ((v 1) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [(c_10_17 m (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 1) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_8_3 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) ((v 3) + ((v 0) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_12 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) ((v 12) + ((v 0) * ((v 19) ^ 2)))).left_comm]

private theorem chunk_63 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 21 (v 21) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 6 (v 6) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_13 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) ((v 13) + ((v 1) * (v 18)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_18 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_19 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_20 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) ((v 18) * ((v 1) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_21 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) (v 21)).left_comm]

private theorem chunk_64 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 21 (v 21) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 6 (v 6) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_21 m ((v 18) * ((v 1) ^ 2)) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 6 ((v 18) * ((v 1) ^ 2)) (v 6),
      show ((v 18) * ((v 1) ^ 2)) + (v 6) = ((v 6) + ((v 18) * ((v 1) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_7 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) ((v 7) + ((v 0) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_5 m (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_5 m ((v 7) + ((v 0) * (v 19))) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_5 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_5 m (v 21) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]

private theorem chunk_65 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 8 (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 11 (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 9 (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) := by
  have h0 : X m 20 (v 20) * X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) = X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * X m 20 (v 20) * X m 14 (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20))) := by
    have h := s_20_5 m (v 20) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))
    rw [show (v 20) * (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) = (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h0]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_5 m (v 19) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]
  have h2 : X m 18 (v 18) * X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) = X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * X m 18 (v 18) * X m 11 (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * X m 9 (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) := by
    have h := s_18_5 m (v 18) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))
    rw [show (v 18) * (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) = (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) by ring, show (v 18) * (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) ^ 2 = (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) by ring_nf; simp [CharTwo.two_eq_zero]] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h2]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_5 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_5 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]
  have h5 : X m 13 ((v 13) + ((v 1) * (v 18))) * X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) = X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * X m 13 ((v 13) + ((v 1) * (v 18))) * X m 8 (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) := by
    have h := s_13_5 m ((v 13) + ((v 1) * (v 18))) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))
    rw [show ((v 13) + ((v 1) * (v 18))) * (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) = (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h5]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_5 m ((v 12) + ((v 0) * ((v 19) ^ 2))) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_3_5 m ((v 3) + ((v 0) * ((v 1) ^ 2))) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]

private theorem chunk_66 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 8 (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 11 (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 9 (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 8 (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 11 (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 9 (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_2_5 m ((v 2) + ((v 0) * (v 1))) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_11_5 m (((v 0) * (v 17)) + ((v 18) * (v 5))) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_10_5 m (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [(c_17_5 m ((v 1) * (v 20)) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2]
    rw [(c_16_5 m (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_18 m (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) (v 18)).left_comm]

private theorem chunk_67 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 8 (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 11 (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 9 (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 11 (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 8 (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_11 m (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_11 m (v 18) (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_11 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_11 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_11 m ((v 13) + ((v 1) * (v 18))) (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_11 m ((v 12) + ((v 0) * ((v 19) ^ 2))) (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_11 m ((v 3) + ((v 0) * ((v 1) ^ 2))) (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_2_11 m ((v 2) + ((v 0) * (v 1))) (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19)))).left_comm]

private theorem chunk_68 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) * (X m 11 (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 8 (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 14 (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 20 (v 20) * (X m 8 (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [add_suffix m 11 (((v 0) * (v 17)) + ((v 18) * (v 5))) (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))),
      show (((v 0) * (v 17)) + ((v 18) * (v 5))) + (((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) = (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_19 m (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_20 m (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_14 m (v 20) (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20)))).left_comm]

private theorem chunk_69 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 20 (v 20) * (X m 8 (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 8 (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_14 m (v 19) (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_14 m (v 18) (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20))),
      show ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2))) + (((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 19) * (v 20))) = ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_21 m (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 6) + ((v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) ((v 6) + ((v 18) * ((v 1) ^ 2)))).left_comm]

private theorem chunk_70 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 8 (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 2 (v 2) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 7) + ((v 0) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_7 m (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) ((v 7) + ((v 0) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))),
      show (((v 1) * (v 13) * (v 7)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) + (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 2) * (v 20))) = (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))),
      show (((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) + ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 1) * (v 18) * (v 5))) = ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))),
      show (((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) + ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2)) + ((v 18) * ((v 0) ^ 2) * ((v 1) ^ 2) * ((v 19) ^ 2))) = ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_2 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) (v 2)).left_comm]

private theorem chunk_71 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 2 (v 2) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 2 (v 2) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 5 ((v 19) * (v 2)) * (X m 20 (v 20) * (X m 11 ((v 2) * (v 20)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_2 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_2 m ((v 7) + ((v 0) * (v 19))) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_2 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (v 2)).left_comm]
  have h3 : X m 21 (v 21) * X m 2 (v 2) = X m 2 (v 2) * X m 21 (v 21) * X m 14 ((v 2) * (v 21)) * X m 9 ((v 21) * ((v 2) ^ 2)) := by
    have h := s_21_2 m (v 21) (v 2)
    rw [show (v 21) * (v 2) = ((v 2) * (v 21)) by ring, show (v 21) * (v 2) ^ 2 = ((v 21) * ((v 2) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h3]
  have h4 : X m 20 (v 20) * X m 2 (v 2) = X m 2 (v 2) * X m 20 (v 20) * X m 11 ((v 2) * (v 20)) := by
    have h := s_20_2 m (v 20) (v 2)
    rw [show (v 20) * (v 2) = ((v 2) * (v 20)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  have h5 : X m 19 (v 19) * X m 2 (v 2) = X m 2 (v 2) * X m 19 (v 19) * X m 5 ((v 19) * (v 2)) := by
    have h := s_19_2 m (v 19) (v 2)
    rw [show (v 19) * (v 2) = ((v 19) * (v 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h5]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_2 m (v 18) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_2 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (v 2)).left_comm]

private theorem chunk_72 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 2) + ((v 0) * (v 1))) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 2 (v 2) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 5 ((v 19) * (v 2)) * (X m 20 (v 20) * (X m 11 ((v 2) * (v 20)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 5 ((v 19) * (v 2)) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 11 ((v 18) * (v 19) * (v 2)) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 11 ((v 2) * (v 20)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_2 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_2 m ((v 13) + ((v 1) * (v 18))) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_2 m ((v 12) + ((v 0) * ((v 19) ^ 2))) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_2 m ((v 3) + ((v 0) * ((v 1) ^ 2))) (v 2)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [add_suffix m 2 ((v 2) + ((v 0) * (v 1))) (v 2),
      show ((v 2) + ((v 0) * (v 1))) + (v 2) = ((v 0) * (v 1)) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_5 m (v 19) ((v 19) * (v 2))).left_comm]
  have h6 : X m 18 (v 18) * X m 5 ((v 19) * (v 2)) = X m 5 ((v 19) * (v 2)) * X m 18 (v 18) * X m 11 ((v 18) * (v 19) * (v 2)) * X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) := by
    have h := s_18_5 m (v 18) ((v 19) * (v 2))
    rw [show (v 18) * ((v 19) * (v 2)) = ((v 18) * (v 19) * (v 2)) by ring, show (v 18) * ((v 19) * (v 2)) ^ 2 = ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h6]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_5 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 19) * (v 2))).left_comm]

private theorem chunk_73 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 5 ((v 19) * (v 2)) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 11 ((v 18) * (v 19) * (v 2)) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 11 ((v 2) * (v 20)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 5 ((v 19) * (v 2)) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 11 ((v 18) * (v 19) * (v 2)) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 11 ((v 2) * (v 20)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_5 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) ((v 19) * (v 2))).left_comm]
  have h1 : X m 13 ((v 13) + ((v 1) * (v 18))) * X m 5 ((v 19) * (v 2)) = X m 5 ((v 19) * (v 2)) * X m 13 ((v 13) + ((v 1) * (v 18))) * X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) := by
    have h := s_13_5 m ((v 13) + ((v 1) * (v 18))) ((v 19) * (v 2))
    rw [show ((v 13) + ((v 1) * (v 18))) * ((v 19) * (v 2)) = (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h1]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_5 m ((v 12) + ((v 0) * ((v 19) ^ 2))) ((v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_5 m ((v 3) + ((v 0) * ((v 1) ^ 2))) ((v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_2_5 m ((v 0) * (v 1)) ((v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_11_5 m (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) ((v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_10_5 m (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_17_5 m ((v 1) * (v 20)) ((v 19) * (v 2))).left_comm]

private theorem chunk_74 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 5 ((v 19) * (v 2)) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 11 ((v 18) * (v 19) * (v 2)) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 11 ((v 2) * (v 20)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 11 ((v 18) * (v 19) * (v 2)) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 11 ((v 2) * (v 20)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2]
    rw [(c_16_5 m (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) ((v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2]
    rw [add_suffix m 5 (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) ((v 19) * (v 2)),
      show (((v 1) * (v 7)) + ((v 0) * (v 1) * (v 19))) + ((v 19) * (v 2)) = (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_18 m (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_11 m (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) ((v 18) * (v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_11 m (v 18) ((v 18) * (v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_11 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 18) * (v 19) * (v 2))).left_comm]

private theorem chunk_75 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 11 ((v 18) * (v 19) * (v 2)) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 11 ((v 2) * (v 20)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 20 (v 20) * (X m 11 ((v 2) * (v 20)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_11 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) ((v 18) * (v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_11 m ((v 13) + ((v 1) * (v 18))) ((v 18) * (v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_11 m ((v 12) + ((v 0) * ((v 19) ^ 2))) ((v 18) * (v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_11 m ((v 3) + ((v 0) * ((v 1) ^ 2))) ((v 18) * (v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_2_11 m ((v 0) * (v 1)) ((v 18) * (v 19) * (v 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [add_suffix m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) ((v 18) * (v 19) * (v 2)),
      show (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 0) * (v 1) * (v 18) * (v 19))) + ((v 18) * (v 19) * (v 2)) = (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_19 m (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 19)).left_comm]

private theorem chunk_76 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 20 (v 20) * (X m 11 ((v 2) * (v 20)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 11 ((v 2) * (v 20)) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 ((v 19) * (v 2) * (v 20)) * (X m 20 (v 20) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_20 m (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_11 m ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) ((v 2) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_11 m (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) ((v 2) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_11 m (v 20) ((v 2) * (v 20))).left_comm]
  have h5 : X m 19 (v 19) * X m 11 ((v 2) * (v 20)) = X m 11 ((v 2) * (v 20)) * X m 19 (v 19) * X m 14 ((v 19) * (v 2) * (v 20)) := by
    have h := s_19_11 m (v 19) ((v 2) * (v 20))
    rw [show (v 19) * ((v 2) * (v 20)) = ((v 19) * (v 2) * (v 20)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h5]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_11 m (v 18) ((v 2) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_11 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 2) * (v 20))).left_comm]

private theorem chunk_77 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 11 ((v 2) * (v 20)) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 ((v 19) * (v 2) * (v 20)) * (X m 20 (v 20) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 14 ((v 19) * (v 2) * (v 20)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_11 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) ((v 2) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_11 m ((v 13) + ((v 1) * (v 18))) ((v 2) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_11 m ((v 12) + ((v 0) * ((v 19) ^ 2))) ((v 2) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_11 m ((v 3) + ((v 0) * ((v 1) ^ 2))) ((v 2) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_2_11 m ((v 0) * (v 1)) ((v 2) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [add_suffix m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) ((v 2) * (v 20)),
      show (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) + ((v 2) * (v 20)) = (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_14 m (v 19) ((v 19) * (v 2) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_14 m (v 18) ((v 19) * (v 2) * (v 20))).left_comm]

private theorem chunk_78 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 14 ((v 19) * (v 2) * (v 20)) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 21 (v 21) * (X m 14 ((v 2) * (v 21)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 ((v 2) * (v 21)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 19) * (v 2) * (v 20))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) ((v 19) * (v 2) * (v 20)),
      show ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) + ((v 19) * (v 2) * (v 20)) = ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_21 m (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) ((v 2) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) ((v 2) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_14 m (v 21) ((v 2) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_14 m (v 20) ((v 2) * (v 21))).left_comm]

private theorem chunk_79 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 ((v 2) * (v 21)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) * (X m 9 ((v 21) * ((v 2) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 9 (((v 21) * ((v 2) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_14 m (v 19) ((v 2) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_14 m (v 18) ((v 2) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 2) * (v 21))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) ((v 2) * (v 21)),
      show ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) + ((v 2) * (v 21)) = ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) ((v 21) * ((v 2) ^ 2)),
      show ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 2) ^ 2)) = (((v 21) * ((v 2) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m (((v 21) * ((v 2) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2))) ((v 6) + ((v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) ((v 6) + ((v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m (((v 21) * ((v 2) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2))) ((v 7) + ((v 0) * (v 19)))).left_comm]

private theorem chunk_80 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 9 (((v 21) * ((v 2) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 3 (v 3) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_7 m (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) ((v 7) + ((v 0) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (((v 21) * ((v 2) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2))) ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))),
      show (((v 13) * (v 19) * (v 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) + ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2))) = ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 (((v 21) * ((v 2) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2))) ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))),
      show (((v 21) * ((v 2) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2))) + ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) = ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_3 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) (v 3)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_3 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 3)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_3 m ((v 7) + ((v 0) * (v 19))) (v 3)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_3 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (v 3)).left_comm]

private theorem chunk_81 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 3 (v 3) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 3 (v 3) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 4 ((v 18) * (v 3)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 8 ((v 20) * (v 3)) * (X m 15 ((v 3) * ((v 20) ^ 2)) * (X m 21 (v 21) * (X m 10 ((v 21) * (v 3)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) := by
  have h0 : X m 21 (v 21) * X m 3 (v 3) = X m 3 (v 3) * X m 21 (v 21) * X m 10 ((v 21) * (v 3)) := by
    have h := s_21_3 m (v 21) (v 3)
    rw [show (v 21) * (v 3) = ((v 21) * (v 3)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h0]
  have h1 : X m 20 (v 20) * X m 3 (v 3) = X m 3 (v 3) * X m 20 (v 20) * X m 8 ((v 20) * (v 3)) * X m 15 ((v 3) * ((v 20) ^ 2)) := by
    have h := s_20_3 m (v 20) (v 3)
    rw [show (v 20) * (v 3) = ((v 20) * (v 3)) by ring, show (v 3) * (v 20) ^ 2 = ((v 3) * ((v 20) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h1]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_3 m (v 19) (v 3)).left_comm]
  have h3 : X m 18 (v 18) * X m 3 (v 3) = X m 3 (v 3) * X m 18 (v 18) * X m 4 ((v 18) * (v 3)) := by
    have h := s_18_3 m (v 18) (v 3)
    rw [show (v 18) * (v 3) = ((v 18) * (v 3)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h3]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_3 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (v 3)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_3 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) (v 3)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_3 m ((v 13) + ((v 1) * (v 18))) (v 3)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_3 m ((v 12) + ((v 0) * ((v 19) ^ 2))) (v 3)).left_comm]

private theorem chunk_82 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) * (X m 3 (v 3) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 4 ((v 18) * (v 3)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 8 ((v 20) * (v 3)) * (X m 15 ((v 3) * ((v 20) ^ 2)) * (X m 21 (v 21) * (X m 10 ((v 21) * (v 3)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) =
      X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 4 ((v 18) * (v 3)) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 8 ((v 20) * (v 3)) * (X m 15 ((v 3) * ((v 20) ^ 2)) * (X m 21 (v 21) * (X m 10 ((v 21) * (v 3)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 3 ((v 3) + ((v 0) * ((v 1) ^ 2))) (v 3),
      show ((v 3) + ((v 0) * ((v 1) ^ 2))) + (v 3) = ((v 0) * ((v 1) ^ 2)) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_4 m (v 18) ((v 18) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_4 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 18) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_4 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) ((v 18) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_4 m ((v 13) + ((v 1) * (v 18))) ((v 18) * (v 3))).left_comm]
  have h5 : X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * X m 4 ((v 18) * (v 3)) = X m 4 ((v 18) * (v 3)) * X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) := by
    have h := s_12_4 m ((v 12) + ((v 0) * ((v 19) ^ 2))) ((v 18) * (v 3))
    rw [show ((v 12) + ((v 0) * ((v 19) ^ 2))) * ((v 18) * (v 3)) = (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h5]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_4 m ((v 0) * ((v 1) ^ 2)) ((v 18) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_2_4 m ((v 0) * (v 1)) ((v 18) * (v 3))).left_comm]

private theorem chunk_83 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 ((v 0) * (v 6)) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 4 ((v 18) * (v 3)) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 8 ((v 20) * (v 3)) * (X m 15 ((v 3) * ((v 20) ^ 2)) * (X m 21 (v 21) * (X m 10 ((v 21) * (v 3)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 8 ((v 20) * (v 3)) * (X m 15 ((v 3) * ((v 20) ^ 2)) * (X m 21 (v 21) * (X m 10 ((v 21) * (v 3)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_11_4 m (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) ((v 18) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_10_4 m (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 18) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_17_4 m ((v 1) * (v 20)) ((v 18) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [(c_16_4 m (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) ((v 18) * (v 3))).left_comm]
  conv_lhs =>
    enter [2]
    rw [(c_5_4 m (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) ((v 18) * (v 3))).left_comm]
  conv_lhs =>
    rw [add_suffix m 4 ((v 0) * (v 6)) ((v 18) * (v 3)),
      show ((v 0) * (v 6)) + ((v 18) * (v 3)) = (((v 0) * (v 6)) + ((v 18) * (v 3))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) ((v 13) + ((v 1) * (v 18)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20)))).left_comm]

private theorem chunk_84 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 8 ((v 20) * (v 3)) * (X m 15 ((v 3) * ((v 20) ^ 2)) * (X m 21 (v 21) * (X m 10 ((v 21) * (v 3)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 15 ((v 3) * ((v 20) ^ 2)) * (X m 20 (v 20) * (X m 8 ((v 20) * (v 3)) * (X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 21 (v 21) * (X m 10 ((v 21) * (v 3)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) ((v 20) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) ((v 3) * ((v 20) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m ((v 20) * (v 3)) ((v 3) * ((v 20) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_15 m (v 20) ((v 3) * ((v 20) ^ 2))).left_comm]

private theorem chunk_85 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 15 ((v 3) * ((v 20) ^ 2)) * (X m 20 (v 20) * (X m 8 ((v 20) * (v 3)) * (X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 21 (v 21) * (X m 10 ((v 21) * (v 3)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 10 ((v 21) * (v 3)) * (X m 21 (v 21) * (X m 8 ((v 20) * (v 3)) * (X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_15 m (v 19) ((v 3) * ((v 20) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m (v 18) ((v 3) * ((v 20) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 3) * ((v 20) ^ 2)),
      show ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) + ((v 3) * ((v 20) ^ 2)) = ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_21 m ((v 20) * (v 3)) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_10 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) ((v 21) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_10 m ((v 20) * (v 3)) ((v 21) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_10 m (v 21) ((v 21) * (v 3))).left_comm]

private theorem chunk_86 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 10 ((v 21) * (v 3)) * (X m 21 (v 21) * (X m 8 ((v 20) * (v 3)) * (X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 10 ((v 21) * (v 3)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 15 ((v 18) * (v 21) * (v 3)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 ((v 20) * (v 3)) * (X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_10 m (v 20) ((v 21) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_10 m (v 19) ((v 21) * (v 3))).left_comm]
  have h2 : X m 18 (v 18) * X m 10 ((v 21) * (v 3)) = X m 10 ((v 21) * (v 3)) * X m 18 (v 18) * X m 15 ((v 18) * (v 21) * (v 3)) := by
    have h := s_18_10 m (v 18) ((v 21) * (v 3))
    rw [show (v 18) * ((v 21) * (v 3)) = ((v 18) * (v 21) * (v 3)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h2]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_10 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 21) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_10 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) ((v 21) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_10 m ((v 13) + ((v 1) * (v 18))) ((v 21) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_10 m ((v 12) + ((v 0) * ((v 19) ^ 2))) ((v 21) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_10 m ((v 0) * ((v 1) ^ 2)) ((v 21) * (v 3))).left_comm]

private theorem chunk_87 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 10 ((v 21) * (v 3)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 15 ((v 18) * (v 21) * (v 3)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 8 ((v 20) * (v 3)) * (X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 8 ((v 20) * (v 3)) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_2_10 m ((v 0) * (v 1)) ((v 21) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_11_10 m (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) ((v 21) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [add_suffix m 10 (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 21) * (v 3)),
      show (((v 16) * ((v 1) ^ 2)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) + ((v 21) * (v 3)) = (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m (v 18) ((v 18) * (v 21) * (v 3))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 18) * (v 21) * (v 3)),
      show ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) + ((v 18) * (v 21) * (v 3)) = ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) ((v 6) + ((v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m ((v 20) * (v 3)) ((v 6) + ((v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) ((v 7) + ((v 0) * (v 19)))).left_comm]

private theorem chunk_88 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 8 ((v 20) * (v 3)) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 12 (v 12) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_7 m ((v 20) * (v 3)) ((v 7) + ((v 0) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 ((v 20) * (v 3)) ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))),
      show ((v 20) * (v 3)) + ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) = ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))),
      show (((v 12) * (v 18) * (v 3)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) + ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 3) * ((v 19) ^ 2))) = ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_12 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) (v 12)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_12 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 12)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_12 m ((v 7) + ((v 0) * (v 19))) (v 12)).left_comm]
  have h7 : X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * X m 12 (v 12) = X m 12 (v 12) * X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) := by
    have h := s_6_12 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (v 12)
    rw [show ((v 6) + ((v 18) * ((v 1) ^ 2))) * (v 12) = (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h7]

private theorem chunk_89 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 12 (v 12) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 (((v 12) * (v 13)) + ((v 1) * (v 12) * (v 18))) * (X m 15 (((v 12) * ((v 13) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 16 ((v 12) * (v 18)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_12 m (v 21) (v 12)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_12 m (v 20) (v 12)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_12 m (v 19) (v 12)).left_comm]
  have h3 : X m 18 (v 18) * X m 12 (v 12) = X m 12 (v 12) * X m 18 (v 18) * X m 16 ((v 12) * (v 18)) := by
    have h := s_18_12 m (v 18) (v 12)
    rw [show (v 18) * (v 12) = ((v 12) * (v 18)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h3]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_12 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (v 12)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_12 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) (v 12)).left_comm]
  have h6 : X m 13 ((v 13) + ((v 1) * (v 18))) * X m 12 (v 12) = X m 12 (v 12) * X m 13 ((v 13) + ((v 1) * (v 18))) * X m 14 (((v 12) * (v 13)) + ((v 1) * (v 12) * (v 18))) * X m 15 (((v 12) * ((v 13) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))) := by
    have h := s_13_12 m ((v 13) + ((v 1) * (v 18))) (v 12)
    rw [show ((v 13) + ((v 1) * (v 18))) * (v 12) = (((v 12) * (v 13)) + ((v 1) * (v 12) * (v 18))) by ring, show (v 12) * ((v 13) + ((v 1) * (v 18))) ^ 2 = (((v 12) * ((v 13) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))) by ring_nf; simp [CharTwo.two_eq_zero]] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h6]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 12 ((v 12) + ((v 0) * ((v 19) ^ 2))) (v 12),
      show ((v 12) + ((v 0) * ((v 19) ^ 2))) + (v 12) = ((v 0) * ((v 19) ^ 2)) by abel_nf; simp [CharTwo.two_eq_zero]]

private theorem chunk_90 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 (((v 12) * (v 13)) + ((v 1) * (v 12) * (v 18))) * (X m 15 (((v 12) * ((v 13) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 16 ((v 12) * (v 18)) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 16 ((v 12) * (v 18)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m (((v 12) * ((v 13) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 (((v 12) * (v 13)) + ((v 1) * (v 12) * (v 18))) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))),
      show (((v 12) * (v 13)) + ((v 1) * (v 12) * (v 18))) + ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) = ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 (((v 12) * ((v 13) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))),
      show (((v 12) * ((v 13) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))) + ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) = ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_16 m (v 18) ((v 12) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_16 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 12) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_16 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) ((v 12) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_16 m ((v 13) + ((v 1) * (v 18))) ((v 12) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_16 m ((v 0) * ((v 19) ^ 2)) ((v 12) * (v 18))).left_comm]

private theorem chunk_91 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 16 ((v 12) * (v 18)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 9 ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))) := by
  have h0 : X m 3 ((v 0) * ((v 1) ^ 2)) * X m 16 ((v 12) * (v 18)) = X m 16 ((v 12) * (v 18)) * X m 3 ((v 0) * ((v 1) ^ 2)) * X m 9 ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) := by
    have h := s_3_16 m ((v 0) * ((v 1) ^ 2)) ((v 12) * (v 18))
    rw [show ((v 0) * ((v 1) ^ 2)) * ((v 12) * (v 18)) = ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h0]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_2_16 m ((v 0) * (v 1)) ((v 12) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_11_16 m (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) ((v 12) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_10_16 m (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 12) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [(c_17_16 m ((v 1) * (v 20)) ((v 12) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2]
    rw [add_suffix m 16 (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) ((v 12) * (v 18)),
      show (((v 0) * (v 21)) + ((v 0) * (v 18) * ((v 19) ^ 2))) + ((v 12) * (v 18)) = (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_12 m ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) ((v 0) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) ((v 13) + ((v 1) * (v 18)))).left_comm]

private theorem chunk_92 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 9 ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * (X m 9 ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) ((v 6) + ((v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_10 m ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))).left_comm]

private theorem chunk_93 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * (X m 9 ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 15 (((v 12) * (v 18) * (v 6)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 9 ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_10 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_10 m (v 21) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_10 m (v 20) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_10 m (v 19) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))).left_comm]
  have h4 : X m 18 (v 18) * X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) = X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * X m 18 (v 18) * X m 15 (((v 12) * (v 18) * (v 6)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))) := by
    have h := s_18_10 m (v 18) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))
    rw [show (v 18) * (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) = (((v 12) * (v 18) * (v 6)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_10 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_10 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_10 m ((v 13) + ((v 1) * (v 18))) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))).left_comm]

private theorem chunk_94 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 10 (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 15 (((v 12) * (v 18) * (v 6)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 9 ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 9 ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_10 m ((v 0) * ((v 19) ^ 2)) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_10 m ((v 0) * ((v 1) ^ 2)) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_2_10 m ((v 0) * (v 1)) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_11_10 m (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [add_suffix m 10 (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))),
      show (((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) + (((v 12) * (v 6)) + ((v 12) * (v 18) * ((v 1) ^ 2))) = (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m (v 18) (((v 12) * (v 18) * (v 6)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (((v 12) * (v 18) * (v 6)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))),
      show ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) + (((v 12) * (v 18) * (v 6)) + ((v 12) * ((v 1) ^ 2) * ((v 18) ^ 2))) = ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) ((v 7) + ((v 0) * (v 19)))).left_comm]

private theorem chunk_95 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 9 ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 13 (v 13) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))),
      show ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2)) + ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2))) = ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_13 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_13 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 13)).left_comm]
  have h4 : X m 7 ((v 7) + ((v 0) * (v 19))) * X m 13 (v 13) = X m 13 (v 13) * X m 7 ((v 7) + ((v 0) * (v 19))) * X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) := by
    have h := s_7_13 m ((v 7) + ((v 0) * (v 19))) (v 13)
    rw [show ((v 7) + ((v 0) * (v 19))) * (v 13) = (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_13 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_13 m (v 21) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_13 m (v 20) (v 13)).left_comm]

private theorem chunk_96 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 13) + ((v 1) * (v 18))) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 13 (v 13) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 17 ((v 13) * (v 19)) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))) := by
  have h0 : X m 19 (v 19) * X m 13 (v 13) = X m 13 (v 13) * X m 19 (v 19) * X m 17 ((v 13) * (v 19)) := by
    have h := s_19_13 m (v 19) (v 13)
    rw [show (v 19) * (v 13) = ((v 13) * (v 19)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h0]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_13 m (v 18) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_13 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_13 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) (v 13)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 13 ((v 13) + ((v 1) * (v 18))) (v 13),
      show ((v 13) + ((v 1) * (v 18))) + (v 13) = ((v 1) * (v 18)) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_17 m (v 19) ((v 13) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_17 m (v 18) ((v 13) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_17 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) ((v 13) * (v 19))).left_comm]

private theorem chunk_97 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 ((v 1) * (v 20)) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 17 ((v 13) * (v 19)) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 8 ((v 0) * (v 1) * (v 13) * (v 19)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_17 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) ((v 13) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_17 m ((v 1) * (v 18)) ((v 13) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_17 m ((v 0) * ((v 19) ^ 2)) ((v 13) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_17 m ((v 0) * ((v 1) ^ 2)) ((v 13) * (v 19))).left_comm]
  have h4 : X m 2 ((v 0) * (v 1)) * X m 17 ((v 13) * (v 19)) = X m 17 ((v 13) * (v 19)) * X m 2 ((v 0) * (v 1)) * X m 8 ((v 0) * (v 1) * (v 13) * (v 19)) := by
    have h := s_2_17 m ((v 0) * (v 1)) ((v 13) * (v 19))
    rw [show ((v 0) * (v 1)) * ((v 13) * (v 19)) = ((v 0) * (v 1) * (v 13) * (v 19)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [swap_suffix h4]
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [(c_11_17 m (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) ((v 13) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2]
    rw [(c_10_17 m (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) ((v 13) * (v 19))).left_comm]
  conv_lhs =>
    enter [2, 2, 2]
    rw [add_suffix m 17 ((v 1) * (v 20)) ((v 13) * (v 19)),
      show ((v 1) * (v 20)) + ((v 13) * (v 19)) = (((v 1) * (v 20)) + ((v 13) * (v 19))) by abel]

private theorem chunk_98 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 8 ((v 0) * (v 1) * (v 13) * (v 19)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 8 ((v 0) * (v 1) * (v 13) * (v 19)) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_3 m ((v 0) * (v 1) * (v 13) * (v 19)) ((v 0) * ((v 1) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_12 m ((v 0) * (v 1) * (v 13) * (v 19)) ((v 0) * ((v 19) ^ 2))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_13 m ((v 0) * (v 1) * (v 13) * (v 19)) ((v 1) * (v 18))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m ((v 0) * (v 1) * (v 13) * (v 19)) ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m ((v 0) * (v 1) * (v 13) * (v 19)) ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_18 m ((v 0) * (v 1) * (v 13) * (v 19)) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_19 m ((v 0) * (v 1) * (v 13) * (v 19)) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_20 m ((v 0) * (v 1) * (v 13) * (v 19)) (v 20)).left_comm]

private theorem chunk_99 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 8 ((v 0) * (v 1) * (v 13) * (v 19)) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 0) * (v 1) * (v 13) * (v 19)) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_21 m ((v 0) * (v 1) * (v 13) * (v 19)) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m ((v 0) * (v 1) * (v 13) * (v 19)) ((v 6) + ((v 18) * ((v 1) ^ 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_7 m ((v 0) * (v 1) * (v 13) * (v 19)) ((v 7) + ((v 0) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_11 m ((v 0) * (v 1) * (v 13) * (v 19)) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_11 m ((v 7) + ((v 0) * (v 19))) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_11 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_11 m (v 21) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_11 m (v 20) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))).left_comm]

private theorem chunk_100 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 0) * (v 1) * (v 13) * (v 19)) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 (((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 13) * (v 19) * (v 7))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 0) * (v 1) * (v 13) * (v 19)) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))) := by
  have h0 : X m 19 (v 19) * X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) = X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * X m 19 (v 19) * X m 14 (((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 13) * (v 19) * (v 7))) := by
    have h := s_19_11 m (v 19) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))
    rw [show (v 19) * (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) = (((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 13) * (v 19) * (v 7))) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix h0]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_11 m (v 18) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_11 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_14_11 m ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_13_11 m ((v 1) * (v 18)) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_12_11 m ((v 0) * ((v 19) ^ 2)) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2]
    rw [(c_3_11 m ((v 0) * ((v 1) ^ 2)) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2]
    rw [(c_2_11 m ((v 0) * (v 1)) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19)))).left_comm]

private theorem chunk_101 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 11 (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 14 (((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 13) * (v 19) * (v 7))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 0) * (v 1) * (v 13) * (v 19)) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 14 (v 14) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2]
    rw [add_suffix m 11 (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))),
      show (((v 0) * (v 17)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) + (((v 13) * (v 7)) + ((v 0) * (v 13) * (v 19))) = (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_14 m (v 19) (((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 13) * (v 19) * (v 7)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_14 m (v 18) (((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 13) * (v 19) * (v 7)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 13) * (v 19) * (v 7)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) (((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 13) * (v 19) * (v 7))),
      show ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) + (((v 0) * (v 13) * ((v 19) ^ 2)) + ((v 13) * (v 19) * (v 7))) = ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 ((v 0) * (v 1) * (v 13) * (v 19)) ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))),
      show ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 1) * (v 13) * (v 19)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) = ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_14 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_14 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 14)).left_comm]

private theorem chunk_102 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 14 (v 14) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_14 m ((v 7) + ((v 0) * (v 19))) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_14 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_14 m (v 21) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_14 m (v 20) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_14 m (v 19) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_14 m (v 18) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_15_14 m ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (v 14)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 14 ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) (v 14),
      show ((v 14) + ((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) + (v 14) = (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) by abel_nf; simp [CharTwo.two_eq_zero]]

private theorem chunk_103 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_15 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) (v 15)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_15 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 15)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_15 m ((v 7) + ((v 0) * (v 19))) (v 15)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_15 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (v 15)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_15 m (v 21) (v 15)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_15 m (v 20) (v 15)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_19_15 m (v 19) (v 15)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_18_15 m (v 18) (v 15)).left_comm]

private theorem chunk_104 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 ((v 18) * (v 19)) * (X m 21 ((v 18) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 15 ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) (v 15),
      show ((v 15) + ((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) + (v 15) = (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_18 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_18 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_18 m ((v 7) + ((v 0) * (v 19))) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_18 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_18 m (v 21) (v 18)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_18 m (v 20) (v 18)).left_comm]
  have h7 : X m 19 (v 19) * X m 18 (v 18) = X m 18 (v 18) * X m 19 (v 19) * X m 20 ((v 18) * (v 19)) * X m 21 ((v 18) * ((v 19) ^ 2)) := by
    have h := s_19_18 m (v 19) (v 18)
    rw [show (v 19) * (v 18) = ((v 18) * (v 19)) by ring, show (v 18) * (v 19) ^ 2 = ((v 18) * ((v 19) ^ 2)) by ring] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h7]

private theorem chunk_105 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 18 (v 18) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 ((v 18) * (v 19)) * (X m 21 ((v 18) * ((v 19) ^ 2)) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 20 ((v 20) + ((v 18) * (v 19))) * (X m 21 ((v 21) + ((v 18) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 18 (v 18) (v 18),
      show (v 18) + (v 18) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_20 m ((v 18) * ((v 19) ^ 2)) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 20 ((v 18) * (v 19)) (v 20),
      show ((v 18) * (v 19)) + (v 20) = ((v 20) + ((v 18) * (v 19))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 21 ((v 18) * ((v 19) ^ 2)) (v 21),
      show ((v 18) * ((v 19) ^ 2)) + (v 21) = ((v 21) + ((v 18) * ((v 19) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_19 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_19 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_19 m ((v 7) + ((v 0) * (v 19))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_19 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (v 19)).left_comm]

private theorem chunk_106 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 20 ((v 20) + ((v 18) * (v 19))) * (X m 21 ((v 21) + ((v 18) * ((v 19) ^ 2))) * (X m 19 (v 19) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 20 ((v 20) + ((v 18) * (v 19))) * (X m 20 (v 20) * (X m 21 ((v 21) + ((v 18) * ((v 19) ^ 2))) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_19 m ((v 21) + ((v 18) * ((v 19) ^ 2))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_20_19 m ((v 20) + ((v 18) * (v 19))) (v 19)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 19 (v 19) (v 19),
      show (v 19) + (v 19) = 0 by abel_nf; simp [CharTwo.two_eq_zero], xz, one_mul]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_20 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_20 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_20 m ((v 7) + ((v 0) * (v 19))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_20 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (v 20)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_21_20 m ((v 21) + ((v 18) * ((v 19) ^ 2))) (v 20)).left_comm]

private theorem chunk_107 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 20 ((v 20) + ((v 18) * (v 19))) * (X m 20 (v 20) * (X m 21 ((v 21) + ((v 18) * ((v 19) ^ 2))) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 20 ((v 18) * (v 19)) * (X m 21 ((v 18) * ((v 19) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 6 (v 6) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 20 ((v 20) + ((v 18) * (v 19))) (v 20),
      show ((v 20) + ((v 18) * (v 19))) + (v 20) = ((v 18) * (v 19)) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_21 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_21 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_7_21 m ((v 7) + ((v 0) * (v 19))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_6_21 m ((v 6) + ((v 18) * ((v 1) ^ 2))) (v 21)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 21 ((v 21) + ((v 18) * ((v 19) ^ 2))) (v 21),
      show ((v 21) + ((v 18) * ((v 19) ^ 2))) + (v 21) = ((v 18) * ((v 19) ^ 2)) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_6 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) (v 6)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_6 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 6)).left_comm]

private theorem chunk_108 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 20 ((v 18) * (v 19)) * (X m 21 ((v 18) * ((v 19) ^ 2)) * (X m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) * (X m 7 ((v 7) + ((v 0) * (v 19))) * (X m 6 (v 6) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 20 ((v 18) * (v 19)) * (X m 21 ((v 18) * ((v 19) ^ 2)) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 6) * ((v 7) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))) := by
  have h0 : X m 7 ((v 7) + ((v 0) * (v 19))) * X m 6 (v 6) = X m 6 (v 6) * X m 7 ((v 7) + ((v 0) * (v 19))) * X m 8 (((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6))) * X m 9 (((v 6) * ((v 7) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) := by
    have h := s_7_6 m ((v 7) + ((v 0) * (v 19))) (v 6)
    rw [show ((v 7) + ((v 0) * (v 19))) * (v 6) = (((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6))) by ring, show (v 6) * ((v 7) + ((v 0) * (v 19))) ^ 2 = (((v 6) * ((v 7) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) by ring_nf; simp [CharTwo.two_eq_zero]] at h
    exact h
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [swap_suffix_two h0]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 6 ((v 6) + ((v 18) * ((v 1) ^ 2))) (v 6),
      show ((v 6) + ((v 18) * ((v 1) ^ 2))) + (v 6) = ((v 18) * ((v 1) ^ 2)) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m (((v 6) * ((v 7) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2)))).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 (((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6))) ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))),
      show (((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6))) + ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) = ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 (((v 6) * ((v 7) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))),
      show (((v 6) * ((v 7) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2))) + ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) = ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 6) * ((v 7) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) by abel]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_7 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 6) * ((v 7) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_8_7 m ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 7)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 7 ((v 7) + ((v 0) * (v 19))) (v 7),
      show ((v 7) + ((v 0) * (v 19))) + (v 7) = ((v 0) * (v 19)) by abel_nf; simp [CharTwo.two_eq_zero]]

private theorem chunk_109 (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 20 ((v 18) * (v 19)) * (X m 21 ((v 18) * ((v 19) ^ 2)) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 7 ((v 0) * (v 19)) * (X m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 6) * ((v 7) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))) =
      X m 4 (((v 0) * (v 6)) + ((v 18) * (v 3))) * (X m 5 (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))) * (X m 16 (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))) * (X m 17 (((v 1) * (v 20)) + ((v 13) * (v 19))) * (X m 10 (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))) * (X m 11 (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))) * (X m 2 ((v 0) * (v 1)) * (X m 3 ((v 0) * ((v 1) ^ 2)) * (X m 12 ((v 0) * ((v 19) ^ 2)) * (X m 13 ((v 1) * (v 18)) * (X m 14 (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))) * (X m 15 (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))) * (X m 20 ((v 18) * (v 19)) * (X m 21 ((v 18) * ((v 19) ^ 2)) * (X m 6 ((v 18) * ((v 1) ^ 2)) * (X m 7 ((v 0) * (v 19)) * (X m 8 (((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) * (X m 9 (((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 6) * ((v 7) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) * (1)))))))))))))))))) := by
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [(c_9_8 m ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 6) * ((v 7) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) (v 8)).left_comm]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 8 ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) (v 8),
      show ((v 8) + ((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) + (v 8) = (((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))) by abel_nf; simp [CharTwo.two_eq_zero]]
  conv_lhs =>
    enter [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [add_suffix m 9 ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 6) * ((v 7) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) (v 9),
      show ((v 9) + ((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 6) * ((v 7) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) + (v 9) = (((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 6) * ((v 7) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))) by abel_nf; simp [CharTwo.two_eq_zero]]

private theorem collected (m : ℕ) (v : Fin 24 → CoefficientField m) :
    X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) =
      splitWord m ![0, 0, ((v 0) * (v 1)), ((v 0) * ((v 1) ^ 2)), (((v 0) * (v 6)) + ((v 18) * (v 3))), (((v 1) * (v 7)) + ((v 19) * (v 2)) + ((v 0) * (v 1) * (v 19))), ((v 18) * ((v 1) ^ 2)), ((v 0) * (v 19)), (((v 1) * (v 11)) + ((v 13) * (v 5)) + ((v 17) * (v 2)) + ((v 19) * (v 4)) + ((v 20) * (v 3)) + ((v 6) * (v 7)) + ((v 0) * (v 19) * (v 6)) + ((v 0) * (v 20) * ((v 1) ^ 2)) + ((v 1) * (v 13) * (v 7)) + ((v 1) * (v 18) * (v 5)) + ((v 1) * (v 2) * (v 20)) + ((v 13) * (v 19) * (v 2)) + ((v 18) * (v 7) * ((v 1) ^ 2)) + ((v 0) * (v 18) * (v 19) * ((v 1) ^ 2)) + ((v 1) * (v 18) * (v 19) * (v 2))), (((v 0) * (v 10)) + ((v 12) * (v 4)) + ((v 16) * (v 3)) + ((v 18) * ((v 5) ^ 2)) + ((v 21) * ((v 2) ^ 2)) + ((v 6) * ((v 7) ^ 2)) + ((v 0) * (v 12) * (v 6)) + ((v 0) * (v 16) * ((v 1) ^ 2)) + ((v 0) * (v 21) * (v 3)) + ((v 0) * (v 4) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 3)) + ((v 18) * ((v 1) ^ 2) * ((v 7) ^ 2)) + ((v 18) * ((v 19) ^ 2) * ((v 2) ^ 2)) + ((v 21) * ((v 0) ^ 2) * ((v 1) ^ 2)) + ((v 6) * ((v 0) ^ 2) * ((v 19) ^ 2)) + ((v 0) * (v 12) * (v 18) * ((v 1) ^ 2))), (((v 12) * (v 6)) + ((v 16) * ((v 1) ^ 2)) + ((v 21) * (v 3)) + ((v 4) * ((v 19) ^ 2)) + ((v 0) * (v 21) * ((v 1) ^ 2)) + ((v 0) * (v 6) * ((v 19) ^ 2)) + ((v 12) * (v 18) * ((v 1) ^ 2)) + ((v 0) * (v 18) * ((v 1) ^ 2) * ((v 19) ^ 2))), (((v 0) * (v 17)) + ((v 13) * (v 7)) + ((v 18) * (v 5)) + ((v 2) * (v 20)) + ((v 0) * (v 13) * (v 19)) + ((v 1) * (v 18) * (v 7)) + ((v 18) * (v 19) * (v 2)) + ((v 0) * (v 1) * (v 18) * (v 19))), ((v 0) * ((v 19) ^ 2)), ((v 1) * (v 18)), (((v 1) * (v 16)) + ((v 11) * (v 19)) + ((v 12) * (v 13)) + ((v 17) * (v 7)) + ((v 2) * (v 21)) + ((v 20) * (v 5)) + ((v 0) * (v 1) * (v 21)) + ((v 1) * (v 12) * (v 18)) + ((v 1) * (v 20) * (v 7)) + ((v 13) * (v 19) * (v 7)) + ((v 19) * (v 2) * (v 20)) + ((v 0) * (v 1) * (v 18) * ((v 19) ^ 2)) + ((v 0) * (v 1) * (v 19) * (v 20))), (((v 0) * ((v 17) ^ 2)) + ((v 10) * (v 18)) + ((v 12) * ((v 13) ^ 2)) + ((v 16) * (v 6)) + ((v 21) * (v 4)) + ((v 3) * ((v 20) ^ 2)) + ((v 0) * (v 21) * (v 6)) + ((v 0) * ((v 13) ^ 2) * ((v 19) ^ 2)) + ((v 12) * (v 18) * (v 6)) + ((v 18) * (v 21) * (v 3)) + ((v 18) * (v 4) * ((v 19) ^ 2)) + ((v 0) * (v 18) * (v 6) * ((v 19) ^ 2))), (((v 0) * (v 21)) + ((v 12) * (v 18)) + ((v 0) * (v 18) * ((v 19) ^ 2))), (((v 1) * (v 20)) + ((v 13) * (v 19))), 0, 0, ((v 18) * (v 19)), ((v 18) * ((v 19) ^ 2)), 0, 0] := by
  have h := (((((((chunk_0 m v).trans ((chunk_1 m v).trans (chunk_2 m v))).trans ((chunk_3 m v).trans ((chunk_4 m v).trans (chunk_5 m v)))).trans (((chunk_6 m v).trans ((chunk_7 m v).trans (chunk_8 m v))).trans (((chunk_9 m v).trans (chunk_10 m v)).trans ((chunk_11 m v).trans (chunk_12 m v))))).trans ((((chunk_13 m v).trans ((chunk_14 m v).trans (chunk_15 m v))).trans (((chunk_16 m v).trans (chunk_17 m v)).trans ((chunk_18 m v).trans (chunk_19 m v)))).trans (((chunk_20 m v).trans ((chunk_21 m v).trans (chunk_22 m v))).trans (((chunk_23 m v).trans (chunk_24 m v)).trans ((chunk_25 m v).trans (chunk_26 m v)))))).trans (((((chunk_27 m v).trans ((chunk_28 m v).trans (chunk_29 m v))).trans (((chunk_30 m v).trans (chunk_31 m v)).trans ((chunk_32 m v).trans (chunk_33 m v)))).trans (((chunk_34 m v).trans ((chunk_35 m v).trans (chunk_36 m v))).trans (((chunk_37 m v).trans (chunk_38 m v)).trans ((chunk_39 m v).trans (chunk_40 m v))))).trans ((((chunk_41 m v).trans ((chunk_42 m v).trans (chunk_43 m v))).trans (((chunk_44 m v).trans (chunk_45 m v)).trans ((chunk_46 m v).trans (chunk_47 m v)))).trans (((chunk_48 m v).trans ((chunk_49 m v).trans (chunk_50 m v))).trans (((chunk_51 m v).trans (chunk_52 m v)).trans ((chunk_53 m v).trans (chunk_54 m v))))))).trans ((((((chunk_55 m v).trans ((chunk_56 m v).trans (chunk_57 m v))).trans ((chunk_58 m v).trans ((chunk_59 m v).trans (chunk_60 m v)))).trans (((chunk_61 m v).trans ((chunk_62 m v).trans (chunk_63 m v))).trans (((chunk_64 m v).trans (chunk_65 m v)).trans ((chunk_66 m v).trans (chunk_67 m v))))).trans ((((chunk_68 m v).trans ((chunk_69 m v).trans (chunk_70 m v))).trans (((chunk_71 m v).trans (chunk_72 m v)).trans ((chunk_73 m v).trans (chunk_74 m v)))).trans (((chunk_75 m v).trans ((chunk_76 m v).trans (chunk_77 m v))).trans (((chunk_78 m v).trans (chunk_79 m v)).trans ((chunk_80 m v).trans (chunk_81 m v)))))).trans (((((chunk_82 m v).trans ((chunk_83 m v).trans (chunk_84 m v))).trans (((chunk_85 m v).trans (chunk_86 m v)).trans ((chunk_87 m v).trans (chunk_88 m v)))).trans (((chunk_89 m v).trans ((chunk_90 m v).trans (chunk_91 m v))).trans (((chunk_92 m v).trans (chunk_93 m v)).trans ((chunk_94 m v).trans (chunk_95 m v))))).trans ((((chunk_96 m v).trans ((chunk_97 m v).trans (chunk_98 m v))).trans (((chunk_99 m v).trans (chunk_100 m v)).trans ((chunk_101 m v).trans (chunk_102 m v)))).trans (((chunk_103 m v).trans ((chunk_104 m v).trans (chunk_105 m v))).trans (((chunk_106 m v).trans (chunk_107 m v)).trans ((chunk_108 m v).trans (chunk_109 m v))))))))
  simpa only [splitWord, Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
    xz, one_mul] using h

/-- Square-one detection at the two endpoint high roots, with no X₈ factor. -/
theorem equations (m : ℕ) (v : Fin 24 → CoefficientField m)
    (h22 : v 22 = 0) (h23 : v 23 = 0) (hsq : splitWord m v ^ 2 = 1) :
    v 0 * v 1 ^ 2 = 0 ∧ v 18 * v 19 ^ 2 = 0 := by
  have hh : X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1)))))))))))))))))))))))))))))))))))))))))))) = 1 := by
    simpa only [splitWord, pow_two, h22, h23, xz, one_mul, mul_assoc] using hsq
  have hz : splitWord m (fun _ => 0) = 1 := by simp only [splitWord, xz, mul_one]
  have hv := splitWord_injective m ((collected m v).symm.trans (hh.trans hz.symm))
  exact ⟨congrFun hv 3, congrFun hv 21⟩

end ReeF4.ElementaryTwoBound.Replacement.EndpointSquares.Collection
