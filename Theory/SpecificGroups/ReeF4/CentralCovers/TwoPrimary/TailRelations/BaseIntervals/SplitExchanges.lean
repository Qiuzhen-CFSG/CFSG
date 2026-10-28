module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus

/-!
# Remaining short angular exchanges in the concrete Ree group

The existing split-root exchange laws collect the nine main-curve pairs not
covered by the normal-generation calculation. The factors include the central
curves of the nonabelian B₂ blocks. Indices are zero based.

Source: GLS3, Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
open Theory.AlgebraicGroup StandardRootSystem
namespace ReeF4.CentralCovers.TwoPrimary.TailRelations.BaseIntervals
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics MatrixRelations MatrixRelations.LongCommutators
open Parabolics.RadicalCoordinates.FixedCoordinates
noncomputable section

private theorem reverse_two {G : Type*} [Group G] {a b c d : G}
    (h : b * a = a * b * c * d) (hc : c * c = 1) (hd : d * d = 1)
    (hcd : Commute c d) : a * b = b * a * c * d := by
  have hcc : (c * d) * (c * d) = 1 := by
    rw [hcd.symm.mul_mul_mul_comm, hc, hd, one_mul]
  calc
    a * b = (a * b * (c * d)) * (c * d) := by rw [mul_assoc, hcc, mul_one]
    _ = b * a * c * d := by
      simpa only [mul_assoc] using congrArg (fun z => z * (c * d)) h.symm

private theorem swap_suffix {G : Type*} [Group G] {a b c : G}
    (h : a * b = b * a * c) (d : G) : a * (b * d) = b * (a * (c * d)) := by
  simpa only [mul_assoc] using congrArg (fun z => z * d) h

private theorem swap_suffix_two {G : Type*} [Group G] {a b c d : G}
    (h : a * b = b * a * c * d) (e : G) :
    a * (b * e) = b * (a * (c * (d * e))) := by
  simpa only [mul_assoc] using congrArg (fun z => z * e) h

private theorem swap_suffix_zero {G : Type*} [Group G] {a b : G}
    (h : a * b = b * a) (d : G) : a * (b * d) = b * (a * d) := by
  simpa only [mul_assoc] using congrArg (fun z => z * d) h

private theorem cancel_suffix {G : Type*} [Group G] {a b : G}
    (h : a * b = 1) (c : G) : a * (b * c) = c := by
  rw [← mul_assoc, h, one_mul]

attribute [local irreducible] X

private theorem e_8_0 (m : ℕ) (a b : CoefficientField m) :
    X m 8 a * X m 0 b = X m 0 b * X m 8 a := by
  exact (xc m 8 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_7_0 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 0 b = X m 0 b * X m 7 a := by
  exact (xc m 7 0 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_6_0 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 0 b = X m 0 b * X m 6 a * X m 4 (a * b) := by
  exact xs m 6 0 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_6_4 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 4 b = X m 4 b * X m 6 a := by
  exact (xc m 6 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_8_1 (m : ℕ) (a b : CoefficientField m) :
    X m 8 a * X m 1 b = X m 1 b * X m 8 a := by
  exact (xc m 8 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_7_1 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 1 b = X m 1 b * X m 7 a * X m 5 (a * b) := by
  exact xs m 7 1 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_6_1 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 1 b = X m 1 b * X m 6 a := by
  exact (xc m 6 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_4_1 (m : ℕ) (a b : CoefficientField m) :
    X m 4 a * X m 1 b = X m 1 b * X m 4 a := by
  exact (xc m 4 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_7_5 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 5 b = X m 5 b * X m 7 a := by
  exact (xc m 7 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_6_5 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 5 b = X m 5 b * X m 6 a := by
  exact (xc m 6 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_8_2 (m : ℕ) (a b : CoefficientField m) :
    X m 8 a * X m 2 b = X m 2 b * X m 8 a := by
  exact (xc m 8 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_7_2 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 2 b = X m 2 b * X m 7 a := by
  exact (xc m 7 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_6_2 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 2 b = X m 2 b * X m 6 a := by
  exact (xc m 6 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_5_2 (m : ℕ) (a b : CoefficientField m) :
    X m 5 a * X m 2 b = X m 2 b * X m 5 a := by
  exact (xc m 5 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_4_2 (m : ℕ) (a b : CoefficientField m) :
    X m 4 a * X m 2 b = X m 2 b * X m 4 a := by
  exact (xc m 4 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_8_4 (m : ℕ) (a b : CoefficientField m) :
    X m 8 a * X m 4 b = X m 4 b * X m 8 a := by
  exact (xc m 8 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_7_4 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 4 b = X m 4 b * X m 7 a := by
  exact (xc m 7 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_5_4 (m : ℕ) (a b : CoefficientField m) :
    X m 5 a * X m 4 b = X m 4 b * X m 5 a := by
  exact (xc m 5 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_8_5 (m : ℕ) (a b : CoefficientField m) :
    X m 8 a * X m 5 b = X m 5 b * X m 8 a := by
  exact (xc m 8 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_14_6 (m : ℕ) (a b : CoefficientField m) :
    X m 14 a * X m 6 b = X m 6 b * X m 14 a := by
  exact (xc m 14 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_13_6 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 6 b = X m 6 b * X m 13 a := by
  exact (xc m 13 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_12_6 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 6 b = X m 6 b * X m 12 a * X m 10 (a * b) := by
  exact xs m 12 6 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_12_10 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 10 b = X m 10 b * X m 12 a := by
  exact (xc m 12 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_14_7 (m : ℕ) (a b : CoefficientField m) :
    X m 14 a * X m 7 b = X m 7 b * X m 14 a := by
  exact (xc m 14 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_13_7 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 7 b = X m 7 b * X m 13 a * X m 11 (a * b) := by
  exact xs m 13 7 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_12_7 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 7 b = X m 7 b * X m 12 a := by
  exact (xc m 12 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_10_7 (m : ℕ) (a b : CoefficientField m) :
    X m 10 a * X m 7 b = X m 7 b * X m 10 a := by
  exact (xc m 10 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_13_11 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 11 b = X m 11 b * X m 13 a := by
  exact (xc m 13 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_12_11 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 11 b = X m 11 b * X m 12 a := by
  exact (xc m 12 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_14_8 (m : ℕ) (a b : CoefficientField m) :
    X m 14 a * X m 8 b = X m 8 b * X m 14 a := by
  exact (xc m 14 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_13_8 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 8 b = X m 8 b * X m 13 a := by
  exact (xc m 13 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_12_8 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 8 b = X m 8 b * X m 12 a := by
  exact (xc m 12 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_11_8 (m : ℕ) (a b : CoefficientField m) :
    X m 11 a * X m 8 b = X m 8 b * X m 11 a := by
  exact (xc m 11 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_10_8 (m : ℕ) (a b : CoefficientField m) :
    X m 10 a * X m 8 b = X m 8 b * X m 10 a := by
  exact (xc m 10 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_14_10 (m : ℕ) (a b : CoefficientField m) :
    X m 14 a * X m 10 b = X m 10 b * X m 14 a := by
  exact (xc m 14 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_13_10 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 10 b = X m 10 b * X m 13 a := by
  exact (xc m 13 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_11_10 (m : ℕ) (a b : CoefficientField m) :
    X m 11 a * X m 10 b = X m 10 b * X m 11 a := by
  exact (xc m 11 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_14_11 (m : ℕ) (a b : CoefficientField m) :
    X m 14 a * X m 11 b = X m 11 b * X m 14 a := by
  exact (xc m 14 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_20_12 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 12 b = X m 12 b * X m 20 a := by
  exact (xc m 20 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_19_12 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 12 b = X m 12 b * X m 19 a := by
  exact (xc m 19 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_18_12 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 12 b = X m 12 b * X m 18 a * X m 16 (a * b) := by
  exact xs m 18 12 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_18_16 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 16 b = X m 16 b * X m 18 a := by
  exact (xc m 18 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_20_13 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 13 b = X m 13 b * X m 20 a := by
  exact (xc m 20 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_19_13 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 13 b = X m 13 b * X m 19 a * X m 17 (a * b) := by
  exact xs m 19 13 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_18_13 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 13 b = X m 13 b * X m 18 a := by
  exact (xc m 18 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_16_13 (m : ℕ) (a b : CoefficientField m) :
    X m 16 a * X m 13 b = X m 13 b * X m 16 a := by
  exact (xc m 16 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_19_17 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 17 b = X m 17 b * X m 19 a := by
  exact (xc m 19 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_18_17 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 17 b = X m 17 b * X m 18 a := by
  exact (xc m 18 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_20_14 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 14 b = X m 14 b * X m 20 a := by
  exact (xc m 20 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_19_14 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 14 b = X m 14 b * X m 19 a := by
  exact (xc m 19 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_18_14 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 14 b = X m 14 b * X m 18 a := by
  exact (xc m 18 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_17_14 (m : ℕ) (a b : CoefficientField m) :
    X m 17 a * X m 14 b = X m 14 b * X m 17 a := by
  exact (xc m 17 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_16_14 (m : ℕ) (a b : CoefficientField m) :
    X m 16 a * X m 14 b = X m 14 b * X m 16 a := by
  exact (xc m 16 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_20_16 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 16 b = X m 16 b * X m 20 a := by
  exact (xc m 20 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_19_16 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 16 b = X m 16 b * X m 19 a := by
  exact (xc m 19 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_17_16 (m : ℕ) (a b : CoefficientField m) :
    X m 17 a * X m 16 b = X m 16 b * X m 17 a := by
  exact (xc m 17 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_20_17 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 17 b = X m 17 b * X m 20 a := by
  exact (xc m 20 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_14_4 (m : ℕ) (a b : CoefficientField m) :
    X m 14 a * X m 4 b = X m 4 b * X m 14 a := by
  exact (xc m 14 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_13_4 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 4 b = X m 4 b * X m 13 a := by
  exact (xc m 13 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_12_4 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 4 b = X m 4 b * X m 12 a * X m 9 (a * b) := by
  exact xs m 12 4 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_12_9 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 9 b = X m 9 b * X m 12 a := by
  exact (xc m 12 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_14_5 (m : ℕ) (a b : CoefficientField m) :
    X m 14 a * X m 5 b = X m 5 b * X m 14 a := by
  exact (xc m 14 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_13_5 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 5 b = X m 5 b * X m 13 a * X m 8 (a * b) := by
  exact xs m 13 5 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_12_5 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 5 b = X m 5 b * X m 12 a := by
  exact (xc m 12 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_9_5 (m : ℕ) (a b : CoefficientField m) :
    X m 9 a * X m 5 b = X m 5 b * X m 9 a := by
  exact (xc m 9 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_9_8 (m : ℕ) (a b : CoefficientField m) :
    X m 9 a * X m 8 b = X m 8 b * X m 9 a := by
  exact (xc m 9 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_14_9 (m : ℕ) (a b : CoefficientField m) :
    X m 14 a * X m 9 b = X m 9 b * X m 14 a := by
  exact (xc m 14 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_13_9 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 9 b = X m 9 b * X m 13 a := by
  exact (xc m 13 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_17_6 (m : ℕ) (a b : CoefficientField m) :
    X m 17 a * X m 6 b = X m 6 b * X m 17 a := by
  exact (xc m 17 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_16_6 (m : ℕ) (a b : CoefficientField m) :
    X m 16 a * X m 6 b = X m 6 b * X m 16 a * X m 15 (a * b) := by
  exact xs m 16 6 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_16_15 (m : ℕ) (a b : CoefficientField m) :
    X m 16 a * X m 15 b = X m 15 b * X m 16 a := by
  exact (xc m 16 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_17_7 (m : ℕ) (a b : CoefficientField m) :
    X m 17 a * X m 7 b = X m 7 b * X m 17 a * X m 14 (a * b) := by
  exact xs m 17 7 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_16_7 (m : ℕ) (a b : CoefficientField m) :
    X m 16 a * X m 7 b = X m 7 b * X m 16 a := by
  exact (xc m 16 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_15_7 (m : ℕ) (a b : CoefficientField m) :
    X m 15 a * X m 7 b = X m 7 b * X m 15 a := by
  exact (xc m 15 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_15_14 (m : ℕ) (a b : CoefficientField m) :
    X m 15 a * X m 14 b = X m 14 b * X m 15 a := by
  exact (xc m 15 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_17_8 (m : ℕ) (a b : CoefficientField m) :
    X m 17 a * X m 8 b = X m 8 b * X m 17 a := by
  exact (xc m 17 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_16_8 (m : ℕ) (a b : CoefficientField m) :
    X m 16 a * X m 8 b = X m 8 b * X m 16 a := by
  exact (xc m 16 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_15_8 (m : ℕ) (a b : CoefficientField m) :
    X m 15 a * X m 8 b = X m 8 b * X m 15 a := by
  exact (xc m 15 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_17_15 (m : ℕ) (a b : CoefficientField m) :
    X m 17 a * X m 15 b = X m 15 b * X m 17 a := by
  exact (xc m 17 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_20_10 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 10 b = X m 10 b * X m 20 a := by
  exact (xc m 20 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_19_10 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 10 b = X m 10 b * X m 19 a := by
  exact (xc m 19 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_18_10 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 10 b = X m 10 b * X m 18 a * X m 15 (a * b) := by
  exact xs m 18 10 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_18_15 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 15 b = X m 15 b * X m 18 a := by
  exact (xc m 18 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_20_11 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 11 b = X m 11 b * X m 20 a := by
  exact (xc m 20 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_19_11 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 11 b = X m 11 b * X m 19 a * X m 14 (a * b) := by
  exact xs m 19 11 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_18_11 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 11 b = X m 11 b * X m 18 a := by
  exact (xc m 18 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_15_11 (m : ℕ) (a b : CoefficientField m) :
    X m 15 a * X m 11 b = X m 11 b * X m 15 a := by
  exact (xc m 15 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_20_15 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 15 b = X m 15 b * X m 20 a := by
  exact (xc m 20 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_19_15 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 15 b = X m 15 b * X m 19 a := by
  exact (xc m 19 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_23_12 (m : ℕ) (a b : CoefficientField m) :
    X m 23 a * X m 12 b = X m 12 b * X m 23 a := by
  exact (xc m 23 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_22_12 (m : ℕ) (a b : CoefficientField m) :
    X m 22 a * X m 12 b = X m 12 b * X m 22 a * X m 21 (a * b) := by
  exact xs m 22 12 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_22_21 (m : ℕ) (a b : CoefficientField m) :
    X m 22 a * X m 21 b = X m 21 b * X m 22 a := by
  exact (xc m 22 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_23_13 (m : ℕ) (a b : CoefficientField m) :
    X m 23 a * X m 13 b = X m 13 b * X m 23 a * X m 20 (a * b) := by
  exact xs m 23 13 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_22_13 (m : ℕ) (a b : CoefficientField m) :
    X m 22 a * X m 13 b = X m 13 b * X m 22 a := by
  exact (xc m 22 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_21_13 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 13 b = X m 13 b * X m 21 a := by
  exact (xc m 21 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_23_20 (m : ℕ) (a b : CoefficientField m) :
    X m 23 a * X m 20 b = X m 20 b * X m 23 a := by
  exact (xc m 23 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_22_20 (m : ℕ) (a b : CoefficientField m) :
    X m 22 a * X m 20 b = X m 20 b * X m 22 a := by
  exact (xc m 22 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_21_20 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 20 b = X m 20 b * X m 21 a := by
  exact (xc m 21 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_23_14 (m : ℕ) (a b : CoefficientField m) :
    X m 23 a * X m 14 b = X m 14 b * X m 23 a := by
  exact (xc m 23 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_22_14 (m : ℕ) (a b : CoefficientField m) :
    X m 22 a * X m 14 b = X m 14 b * X m 22 a := by
  exact (xc m 22 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_21_14 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 14 b = X m 14 b * X m 21 a := by
  exact (xc m 21 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_23_21 (m : ℕ) (a b : CoefficientField m) :
    X m 23 a * X m 21 b = X m 21 b * X m 23 a := by
  exact (xc m 23 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_20_4 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 4 b = X m 4 b * X m 20 a := by
  exact (xc m 20 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_19_4 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 4 b = X m 4 b * X m 19 a * X m 8 (b * a) * X m 10 (b * a ^ 2) := by
  exact xb m 4 19 8 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem e_18_4 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 4 b = X m 4 b * X m 18 a := by
  exact (xc m 18 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_19_8 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 8 b = X m 8 b * X m 19 a := by
  exact (xc m 19 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_18_8 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 8 b = X m 8 b * X m 18 a := by
  exact (xc m 18 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_20_5 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 5 b = X m 5 b * X m 20 a * X m 14 (a * b) := by
  exact xs m 20 5 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_19_5 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 5 b = X m 5 b * X m 19 a := by
  exact (xc m 19 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_18_5 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 5 b = X m 5 b * X m 18 a * X m 11 (a * b) * X m 9 (a * b ^ 2) := by
  exact reverse_two (xb m 18 5 11 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b) (xx m 11 _) (xx m 9 _) (xc m 11 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) _ _)

private theorem e_15_5 (m : ℕ) (a b : CoefficientField m) :
    X m 15 a * X m 5 b = X m 5 b * X m 15 a := by
  exact (xc m 15 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_10_5 (m : ℕ) (a b : CoefficientField m) :
    X m 10 a * X m 5 b = X m 5 b * X m 10 a := by
  exact (xc m 10 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_18_9 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 9 b = X m 9 b * X m 18 a := by
  exact (xc m 18 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_15_9 (m : ℕ) (a b : CoefficientField m) :
    X m 15 a * X m 9 b = X m 9 b * X m 15 a := by
  exact (xc m 15 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_11_9 (m : ℕ) (a b : CoefficientField m) :
    X m 11 a * X m 9 b = X m 9 b * X m 11 a := by
  exact (xc m 11 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_10_9 (m : ℕ) (a b : CoefficientField m) :
    X m 10 a * X m 9 b = X m 9 b * X m 10 a := by
  exact (xc m 10 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_15_10 (m : ℕ) (a b : CoefficientField m) :
    X m 15 a * X m 10 b = X m 10 b * X m 15 a := by
  exact (xc m 15 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_20_9 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 9 b = X m 9 b * X m 20 a := by
  exact (xc m 20 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_19_9 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 9 b = X m 9 b * X m 19 a := by
  exact (xc m 19 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_20_8 (m : ℕ) (a b : CoefficientField m) :
    X m 20 a * X m 8 b = X m 8 b * X m 20 a := by
  exact (xc m 20 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_23_6 (m : ℕ) (a b : CoefficientField m) :
    X m 23 a * X m 6 b = X m 6 b * X m 23 a * X m 17 (b * a) * X m 21 (b * a ^ 2) := by
  exact xb m 6 23 17 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem e_22_6 (m : ℕ) (a b : CoefficientField m) :
    X m 22 a * X m 6 b = X m 6 b * X m 22 a := by
  exact (xc m 22 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_23_17 (m : ℕ) (a b : CoefficientField m) :
    X m 23 a * X m 17 b = X m 17 b * X m 23 a := by
  exact (xc m 23 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_22_17 (m : ℕ) (a b : CoefficientField m) :
    X m 22 a * X m 17 b = X m 17 b * X m 22 a := by
  exact (xc m 22 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_23_7 (m : ℕ) (a b : CoefficientField m) :
    X m 23 a * X m 7 b = X m 7 b * X m 23 a := by
  exact (xc m 23 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_22_7 (m : ℕ) (a b : CoefficientField m) :
    X m 22 a * X m 7 b = X m 7 b * X m 22 a * X m 20 (a * b) * X m 16 (a * b ^ 2) := by
  exact reverse_two (xb m 22 7 20 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b) (xx m 20 _) (xx m 16 _) (xc m 20 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) _ _)

private theorem e_21_7 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 7 b = X m 7 b * X m 21 a := by
  exact (xc m 21 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_22_16 (m : ℕ) (a b : CoefficientField m) :
    X m 22 a * X m 16 b = X m 16 b * X m 22 a := by
  exact (xc m 22 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_21_16 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 16 b = X m 16 b * X m 21 a := by
  exact (xc m 21 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_23_8 (m : ℕ) (a b : CoefficientField m) :
    X m 23 a * X m 8 b = X m 8 b * X m 23 a * X m 14 (a * b) := by
  exact xs m 23 8 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem e_22_8 (m : ℕ) (a b : CoefficientField m) :
    X m 22 a * X m 8 b = X m 8 b * X m 22 a := by
  exact (xc m 22 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_21_8 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 8 b = X m 8 b * X m 21 a := by
  exact (xc m 21 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_23_16 (m : ℕ) (a b : CoefficientField m) :
    X m 23 a * X m 16 b = X m 16 b * X m 23 a := by
  exact (xc m 23 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

private theorem e_21_17 (m : ℕ) (a b : CoefficientField m) :
    X m 21 a * X m 17 b = X m 17 b * X m 21 a := by
  exact (xc m 21 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b).eq

theorem collect_0_2 (m : ℕ) (t s u v : CoefficientField m) :
    X m 0 (t) * X m 1 (s) * X m 2 (t * s) * X m 6 (u) * X m 7 (v) * X m 8 (u * v) =
      X m 6 (u) * X m 7 (v) * X m 8 (u * v) * X m 0 (t) * X m 1 (s) * X m 2 (t * s) * X m 4 (t * u) * X m 5 (s * v) := by
  symm
  simp only [mul_assoc]
  rw [swap_suffix_zero (e_8_0 m (u * v) (t))]
  rw [swap_suffix_zero (e_7_0 m (v) (t))]
  rw [swap_suffix (e_6_0 m (u) (t))]
  rw [swap_suffix_zero (e_6_4 m (u) ((u) * (t)))]
  rw [swap_suffix_zero (e_8_1 m (u * v) (s))]
  rw [swap_suffix (e_7_1 m (v) (s))]
  rw [swap_suffix_zero (e_6_1 m (u) (s))]
  rw [swap_suffix_zero (e_4_1 m ((u) * (t)) (s))]
  rw [swap_suffix_zero (e_7_5 m (v) ((v) * (s)))]
  rw [swap_suffix_zero (e_6_5 m (u) ((v) * (s)))]
  rw [swap_suffix_zero (e_8_2 m (u * v) (t * s))]
  rw [swap_suffix_zero (e_7_2 m (v) (t * s))]
  rw [swap_suffix_zero (e_6_2 m (u) (t * s))]
  rw [swap_suffix_zero (e_5_2 m ((v) * (s)) (t * s))]
  rw [swap_suffix_zero (e_4_2 m ((u) * (t)) (t * s))]
  rw [swap_suffix_zero (e_8_4 m (u * v) (t * u))]
  rw [swap_suffix_zero (e_7_4 m (v) (t * u))]
  rw [swap_suffix_zero (e_6_4 m (u) (t * u))]
  rw [swap_suffix_zero (e_5_4 m ((v) * (s)) (t * u))]
  rw [cancel_suffix (show X m 4 ((u) * (t)) * X m 4 (t * u) = 1 by rw [show (t * u) = ((u) * (t)) by ring]; exact xx m 4 _)]
  rw [e_8_5 m (u * v) (s * v)]
  rw [swap_suffix_zero (e_7_5 m (v) (s * v))]
  rw [swap_suffix_zero (e_6_5 m (u) (s * v))]
  rw [cancel_suffix (show X m 5 ((v) * (s)) * X m 5 (s * v) = 1 by rw [show (s * v) = ((v) * (s)) by ring]; exact xx m 5 _)]

theorem collect_2_4 (m : ℕ) (t s u v : CoefficientField m) :
    X m 6 (t) * X m 7 (s) * X m 8 (t * s) * X m 12 (u) * X m 13 (v) * X m 14 (u * v) =
      X m 12 (u) * X m 13 (v) * X m 14 (u * v) * X m 6 (t) * X m 7 (s) * X m 8 (t * s) * X m 10 (t * u) * X m 11 (s * v) := by
  symm
  simp only [mul_assoc]
  rw [swap_suffix_zero (e_14_6 m (u * v) (t))]
  rw [swap_suffix_zero (e_13_6 m (v) (t))]
  rw [swap_suffix (e_12_6 m (u) (t))]
  rw [swap_suffix_zero (e_12_10 m (u) ((u) * (t)))]
  rw [swap_suffix_zero (e_14_7 m (u * v) (s))]
  rw [swap_suffix (e_13_7 m (v) (s))]
  rw [swap_suffix_zero (e_12_7 m (u) (s))]
  rw [swap_suffix_zero (e_10_7 m ((u) * (t)) (s))]
  rw [swap_suffix_zero (e_13_11 m (v) ((v) * (s)))]
  rw [swap_suffix_zero (e_12_11 m (u) ((v) * (s)))]
  rw [swap_suffix_zero (e_14_8 m (u * v) (t * s))]
  rw [swap_suffix_zero (e_13_8 m (v) (t * s))]
  rw [swap_suffix_zero (e_12_8 m (u) (t * s))]
  rw [swap_suffix_zero (e_11_8 m ((v) * (s)) (t * s))]
  rw [swap_suffix_zero (e_10_8 m ((u) * (t)) (t * s))]
  rw [swap_suffix_zero (e_14_10 m (u * v) (t * u))]
  rw [swap_suffix_zero (e_13_10 m (v) (t * u))]
  rw [swap_suffix_zero (e_12_10 m (u) (t * u))]
  rw [swap_suffix_zero (e_11_10 m ((v) * (s)) (t * u))]
  rw [cancel_suffix (show X m 10 ((u) * (t)) * X m 10 (t * u) = 1 by rw [show (t * u) = ((u) * (t)) by ring]; exact xx m 10 _)]
  rw [e_14_11 m (u * v) (s * v)]
  rw [swap_suffix_zero (e_13_11 m (v) (s * v))]
  rw [swap_suffix_zero (e_12_11 m (u) (s * v))]
  rw [cancel_suffix (show X m 11 ((v) * (s)) * X m 11 (s * v) = 1 by rw [show (s * v) = ((v) * (s)) by ring]; exact xx m 11 _)]

theorem collect_4_6 (m : ℕ) (t s u v : CoefficientField m) :
    X m 12 (t) * X m 13 (s) * X m 14 (t * s) * X m 18 (u) * X m 19 (v) * X m 20 (u * v) =
      X m 18 (u) * X m 19 (v) * X m 20 (u * v) * X m 12 (t) * X m 13 (s) * X m 14 (t * s) * X m 16 (t * u) * X m 17 (s * v) := by
  symm
  simp only [mul_assoc]
  rw [swap_suffix_zero (e_20_12 m (u * v) (t))]
  rw [swap_suffix_zero (e_19_12 m (v) (t))]
  rw [swap_suffix (e_18_12 m (u) (t))]
  rw [swap_suffix_zero (e_18_16 m (u) ((u) * (t)))]
  rw [swap_suffix_zero (e_20_13 m (u * v) (s))]
  rw [swap_suffix (e_19_13 m (v) (s))]
  rw [swap_suffix_zero (e_18_13 m (u) (s))]
  rw [swap_suffix_zero (e_16_13 m ((u) * (t)) (s))]
  rw [swap_suffix_zero (e_19_17 m (v) ((v) * (s)))]
  rw [swap_suffix_zero (e_18_17 m (u) ((v) * (s)))]
  rw [swap_suffix_zero (e_20_14 m (u * v) (t * s))]
  rw [swap_suffix_zero (e_19_14 m (v) (t * s))]
  rw [swap_suffix_zero (e_18_14 m (u) (t * s))]
  rw [swap_suffix_zero (e_17_14 m ((v) * (s)) (t * s))]
  rw [swap_suffix_zero (e_16_14 m ((u) * (t)) (t * s))]
  rw [swap_suffix_zero (e_20_16 m (u * v) (t * u))]
  rw [swap_suffix_zero (e_19_16 m (v) (t * u))]
  rw [swap_suffix_zero (e_18_16 m (u) (t * u))]
  rw [swap_suffix_zero (e_17_16 m ((v) * (s)) (t * u))]
  rw [cancel_suffix (show X m 16 ((u) * (t)) * X m 16 (t * u) = 1 by rw [show (t * u) = ((u) * (t)) by ring]; exact xx m 16 _)]
  rw [e_20_17 m (u * v) (s * v)]
  rw [swap_suffix_zero (e_19_17 m (v) (s * v))]
  rw [swap_suffix_zero (e_18_17 m (u) (s * v))]
  rw [cancel_suffix (show X m 17 ((v) * (s)) * X m 17 (s * v) = 1 by rw [show (s * v) = ((v) * (s)) by ring]; exact xx m 17 _)]

theorem collect_1_4 (m : ℕ) (t s u v : CoefficientField m) :
    X m 4 (t) * X m 5 (s) * X m 12 (u) * X m 13 (v) * X m 14 (u * v) =
      X m 12 (u) * X m 13 (v) * X m 14 (u * v) * X m 4 (t) * X m 5 (s) * X m 9 (t * u) * X m 8 (s * v) := by
  symm
  simp only [mul_assoc]
  rw [swap_suffix_zero (e_14_4 m (u * v) (t))]
  rw [swap_suffix_zero (e_13_4 m (v) (t))]
  rw [swap_suffix (e_12_4 m (u) (t))]
  rw [swap_suffix_zero (e_12_9 m (u) ((u) * (t)))]
  rw [swap_suffix_zero (e_14_5 m (u * v) (s))]
  rw [swap_suffix (e_13_5 m (v) (s))]
  rw [swap_suffix_zero (e_12_5 m (u) (s))]
  rw [swap_suffix_zero (e_9_5 m ((u) * (t)) (s))]
  rw [swap_suffix_zero (e_13_8 m (v) ((v) * (s)))]
  rw [swap_suffix_zero (e_12_8 m (u) ((v) * (s)))]
  rw [swap_suffix_zero (e_9_8 m ((u) * (t)) ((v) * (s)))]
  rw [swap_suffix_zero (e_14_9 m (u * v) (t * u))]
  rw [swap_suffix_zero (e_13_9 m (v) (t * u))]
  rw [swap_suffix_zero (e_12_9 m (u) (t * u))]
  rw [cancel_suffix (show X m 9 ((u) * (t)) * X m 9 (t * u) = 1 by rw [show (t * u) = ((u) * (t)) by ring]; exact xx m 9 _)]
  rw [e_14_8 m (u * v) (s * v)]
  rw [swap_suffix_zero (e_13_8 m (v) (s * v))]
  rw [swap_suffix_zero (e_12_8 m (u) (s * v))]
  rw [cancel_suffix (show X m 8 ((v) * (s)) * X m 8 (s * v) = 1 by rw [show (s * v) = ((v) * (s)) by ring]; exact xx m 8 _)]

theorem collect_2_5 (m : ℕ) (t s u v : CoefficientField m) :
    X m 6 (t) * X m 7 (s) * X m 8 (t * s) * X m 16 (u) * X m 17 (v) =
      X m 16 (u) * X m 17 (v) * X m 6 (t) * X m 7 (s) * X m 8 (t * s) * X m 15 (t * u) * X m 14 (s * v) := by
  symm
  simp only [mul_assoc]
  rw [swap_suffix_zero (e_17_6 m (v) (t))]
  rw [swap_suffix (e_16_6 m (u) (t))]
  rw [swap_suffix_zero (e_16_15 m (u) ((u) * (t)))]
  rw [swap_suffix (e_17_7 m (v) (s))]
  rw [swap_suffix_zero (e_16_7 m (u) (s))]
  rw [swap_suffix_zero (e_15_7 m ((u) * (t)) (s))]
  rw [swap_suffix_zero (e_17_14 m (v) ((v) * (s)))]
  rw [swap_suffix_zero (e_16_14 m (u) ((v) * (s)))]
  rw [swap_suffix_zero (e_15_14 m ((u) * (t)) ((v) * (s)))]
  rw [swap_suffix_zero (e_17_8 m (v) (t * s))]
  rw [swap_suffix_zero (e_16_8 m (u) (t * s))]
  rw [swap_suffix_zero (e_15_8 m ((u) * (t)) (t * s))]
  rw [swap_suffix_zero (e_14_8 m ((v) * (s)) (t * s))]
  rw [swap_suffix_zero (e_17_15 m (v) (t * u))]
  rw [swap_suffix_zero (e_16_15 m (u) (t * u))]
  rw [cancel_suffix (show X m 15 ((u) * (t)) * X m 15 (t * u) = 1 by rw [show (t * u) = ((u) * (t)) by ring]; exact xx m 15 _)]
  rw [e_17_14 m (v) (s * v)]
  rw [swap_suffix_zero (e_16_14 m (u) (s * v))]
  rw [cancel_suffix (show X m 14 ((v) * (s)) * X m 14 (s * v) = 1 by rw [show (s * v) = ((v) * (s)) by ring]; exact xx m 14 _)]

theorem collect_3_6 (m : ℕ) (t s u v : CoefficientField m) :
    X m 10 (t) * X m 11 (s) * X m 18 (u) * X m 19 (v) * X m 20 (u * v) =
      X m 18 (u) * X m 19 (v) * X m 20 (u * v) * X m 10 (t) * X m 11 (s) * X m 15 (t * u) * X m 14 (s * v) := by
  symm
  simp only [mul_assoc]
  rw [swap_suffix_zero (e_20_10 m (u * v) (t))]
  rw [swap_suffix_zero (e_19_10 m (v) (t))]
  rw [swap_suffix (e_18_10 m (u) (t))]
  rw [swap_suffix_zero (e_18_15 m (u) ((u) * (t)))]
  rw [swap_suffix_zero (e_20_11 m (u * v) (s))]
  rw [swap_suffix (e_19_11 m (v) (s))]
  rw [swap_suffix_zero (e_18_11 m (u) (s))]
  rw [swap_suffix_zero (e_15_11 m ((u) * (t)) (s))]
  rw [swap_suffix_zero (e_19_14 m (v) ((v) * (s)))]
  rw [swap_suffix_zero (e_18_14 m (u) ((v) * (s)))]
  rw [swap_suffix_zero (e_15_14 m ((u) * (t)) ((v) * (s)))]
  rw [swap_suffix_zero (e_20_15 m (u * v) (t * u))]
  rw [swap_suffix_zero (e_19_15 m (v) (t * u))]
  rw [swap_suffix_zero (e_18_15 m (u) (t * u))]
  rw [cancel_suffix (show X m 15 ((u) * (t)) * X m 15 (t * u) = 1 by rw [show (t * u) = ((u) * (t)) by ring]; exact xx m 15 _)]
  rw [e_20_14 m (u * v) (s * v)]
  rw [swap_suffix_zero (e_19_14 m (v) (s * v))]
  rw [swap_suffix_zero (e_18_14 m (u) (s * v))]
  rw [cancel_suffix (show X m 14 ((v) * (s)) * X m 14 (s * v) = 1 by rw [show (s * v) = ((v) * (s)) by ring]; exact xx m 14 _)]

theorem collect_4_7 (m : ℕ) (t s u v : CoefficientField m) :
    X m 12 (t) * X m 13 (s) * X m 14 (t * s) * X m 22 (u) * X m 23 (v) =
      X m 22 (u) * X m 23 (v) * X m 12 (t) * X m 13 (s) * X m 14 (t * s) * X m 21 (t * u) * X m 20 (s * v) := by
  symm
  simp only [mul_assoc]
  rw [swap_suffix_zero (e_23_12 m (v) (t))]
  rw [swap_suffix (e_22_12 m (u) (t))]
  rw [swap_suffix_zero (e_22_21 m (u) ((u) * (t)))]
  rw [swap_suffix (e_23_13 m (v) (s))]
  rw [swap_suffix_zero (e_22_13 m (u) (s))]
  rw [swap_suffix_zero (e_21_13 m ((u) * (t)) (s))]
  rw [swap_suffix_zero (e_23_20 m (v) ((v) * (s)))]
  rw [swap_suffix_zero (e_22_20 m (u) ((v) * (s)))]
  rw [swap_suffix_zero (e_21_20 m ((u) * (t)) ((v) * (s)))]
  rw [swap_suffix_zero (e_23_14 m (v) (t * s))]
  rw [swap_suffix_zero (e_22_14 m (u) (t * s))]
  rw [swap_suffix_zero (e_21_14 m ((u) * (t)) (t * s))]
  rw [swap_suffix_zero (e_20_14 m ((v) * (s)) (t * s))]
  rw [swap_suffix_zero (e_23_21 m (v) (t * u))]
  rw [swap_suffix_zero (e_22_21 m (u) (t * u))]
  rw [cancel_suffix (show X m 21 ((u) * (t)) * X m 21 (t * u) = 1 by rw [show (t * u) = ((u) * (t)) by ring]; exact xx m 21 _)]
  rw [e_23_20 m (v) (s * v)]
  rw [swap_suffix_zero (e_22_20 m (u) (s * v))]
  rw [cancel_suffix (show X m 20 ((v) * (s)) * X m 20 (s * v) = 1 by rw [show (s * v) = ((v) * (s)) by ring]; exact xx m 20 _)]

theorem collect_1_6 (m : ℕ) (t s u v : CoefficientField m) :
    X m 4 (t) * X m 5 (s) * X m 18 (u) * X m 19 (v) * X m 20 (u * v) =
      X m 18 (u) * X m 19 (v) * X m 20 (u * v) * X m 4 (t) * X m 5 (s) * X m 10 (t * v ^ 2) * X m 11 (s * u) * X m 9 (s ^ 2 * u) * X m 8 (t * v) := by
  symm
  simp only [mul_assoc]
  rw [swap_suffix_zero (e_20_4 m (u * v) (t))]
  rw [swap_suffix_two (e_19_4 m (v) (t))]
  rw [swap_suffix_zero (e_18_4 m (u) (t))]
  rw [swap_suffix_zero (e_19_8 m (v) ((t) * (v)))]
  rw [swap_suffix_zero (e_18_8 m (u) ((t) * (v)))]
  rw [swap_suffix_zero (e_19_10 m (v) ((t) * (v) ^ 2))]
  rw [swap_suffix (e_18_10 m (u) ((t) * (v) ^ 2))]
  rw [swap_suffix_zero (e_18_15 m (u) ((u) * ((t) * (v) ^ 2)))]
  rw [swap_suffix (e_20_5 m (u * v) (s))]
  rw [swap_suffix_zero (e_19_5 m (v) (s))]
  rw [swap_suffix_two (e_18_5 m (u) (s))]
  rw [swap_suffix_zero (e_15_5 m ((u) * ((t) * (v) ^ 2)) (s))]
  rw [swap_suffix_zero (e_10_5 m ((t) * (v) ^ 2) (s))]
  rw [swap_suffix_zero (e_8_5 m ((t) * (v)) (s))]
  rw [swap_suffix_zero (e_18_11 m (u) ((u) * (s)))]
  rw [swap_suffix_zero (e_15_11 m ((u) * ((t) * (v) ^ 2)) ((u) * (s)))]
  rw [swap_suffix_zero (e_18_9 m (u) ((u) * (s) ^ 2))]
  rw [swap_suffix_zero (e_15_9 m ((u) * ((t) * (v) ^ 2)) ((u) * (s) ^ 2))]
  rw [swap_suffix_zero (e_11_9 m ((u) * (s)) ((u) * (s) ^ 2))]
  rw [swap_suffix_zero (e_10_9 m ((t) * (v) ^ 2) ((u) * (s) ^ 2))]
  rw [swap_suffix_zero (e_20_14 m (u * v) ((u * v) * (s)))]
  rw [swap_suffix_zero (e_19_14 m (v) ((u * v) * (s)))]
  rw [swap_suffix_zero (e_18_14 m (u) ((u * v) * (s)))]
  rw [swap_suffix_zero (e_15_14 m ((u) * ((t) * (v) ^ 2)) ((u * v) * (s)))]
  rw [swap_suffix_zero (e_20_10 m (u * v) (t * v ^ 2))]
  rw [swap_suffix_zero (e_19_10 m (v) (t * v ^ 2))]
  rw [swap_suffix (e_18_10 m (u) (t * v ^ 2))]
  rw [swap_suffix_zero (e_15_10 m ((u) * ((t) * (v) ^ 2)) (t * v ^ 2))]
  rw [swap_suffix_zero (e_14_10 m ((u * v) * (s)) (t * v ^ 2))]
  rw [swap_suffix_zero (e_11_10 m ((u) * (s)) (t * v ^ 2))]
  rw [cancel_suffix (show X m 10 ((t) * (v) ^ 2) * X m 10 (t * v ^ 2) = 1 by rw [show (t * v ^ 2) = ((t) * (v) ^ 2) by ring]; exact xx m 10 _)]
  rw [swap_suffix_zero (e_18_15 m (u) ((u) * (t * v ^ 2)))]
  rw [cancel_suffix (show X m 15 ((u) * ((t) * (v) ^ 2)) * X m 15 ((u) * (t * v ^ 2)) = 1 by rw [show ((u) * (t * v ^ 2)) = ((u) * ((t) * (v) ^ 2)) by ring]; exact xx m 15 _)]
  rw [swap_suffix_zero (e_20_11 m (u * v) (s * u))]
  rw [swap_suffix (e_19_11 m (v) (s * u))]
  rw [swap_suffix_zero (e_18_11 m (u) (s * u))]
  rw [swap_suffix_zero (e_14_11 m ((u * v) * (s)) (s * u))]
  rw [cancel_suffix (show X m 11 ((u) * (s)) * X m 11 (s * u) = 1 by rw [show (s * u) = ((u) * (s)) by ring]; exact xx m 11 _)]
  rw [swap_suffix_zero (e_19_14 m (v) ((v) * (s * u)))]
  rw [swap_suffix_zero (e_18_14 m (u) ((v) * (s * u)))]
  rw [cancel_suffix (show X m 14 ((u * v) * (s)) * X m 14 ((v) * (s * u)) = 1 by rw [show ((v) * (s * u)) = ((u * v) * (s)) by ring]; exact xx m 14 _)]
  rw [swap_suffix_zero (e_20_9 m (u * v) (s ^ 2 * u))]
  rw [swap_suffix_zero (e_19_9 m (v) (s ^ 2 * u))]
  rw [swap_suffix_zero (e_18_9 m (u) (s ^ 2 * u))]
  rw [cancel_suffix (show X m 9 ((u) * (s) ^ 2) * X m 9 (s ^ 2 * u) = 1 by rw [show (s ^ 2 * u) = ((u) * (s) ^ 2) by ring]; exact xx m 9 _)]
  rw [e_20_8 m (u * v) (t * v)]
  rw [swap_suffix_zero (e_19_8 m (v) (t * v))]
  rw [swap_suffix_zero (e_18_8 m (u) (t * v))]
  rw [cancel_suffix (show X m 8 ((t) * (v)) * X m 8 (t * v) = 1 by rw [show (t * v) = ((t) * (v)) by ring]; exact xx m 8 _)]

theorem collect_2_7 (m : ℕ) (t s u v : CoefficientField m) :
    X m 6 (t) * X m 7 (s) * X m 8 (t * s) * X m 22 (u) * X m 23 (v) =
      X m 22 (u) * X m 23 (v) * X m 6 (t) * X m 7 (s) * X m 8 (t * s) * X m 16 (s ^ 2 * u) * X m 17 (t * v) * X m 21 (t * v ^ 2) * X m 20 (s * u) := by
  symm
  simp only [mul_assoc]
  rw [swap_suffix_two (e_23_6 m (v) (t))]
  rw [swap_suffix_zero (e_22_6 m (u) (t))]
  rw [swap_suffix_zero (e_23_17 m (v) ((t) * (v)))]
  rw [swap_suffix_zero (e_22_17 m (u) ((t) * (v)))]
  rw [swap_suffix_zero (e_23_21 m (v) ((t) * (v) ^ 2))]
  rw [swap_suffix_zero (e_22_21 m (u) ((t) * (v) ^ 2))]
  rw [swap_suffix_zero (e_23_7 m (v) (s))]
  rw [swap_suffix_two (e_22_7 m (u) (s))]
  rw [swap_suffix_zero (e_21_7 m ((t) * (v) ^ 2) (s))]
  rw [swap_suffix (e_17_7 m ((t) * (v)) (s))]
  rw [swap_suffix_zero (e_17_14 m ((t) * (v)) (((t) * (v)) * (s)))]
  rw [swap_suffix_zero (e_22_20 m (u) ((u) * (s)))]
  rw [swap_suffix_zero (e_21_20 m ((t) * (v) ^ 2) ((u) * (s)))]
  rw [swap_suffix_zero (e_22_16 m (u) ((u) * (s) ^ 2))]
  rw [swap_suffix_zero (e_21_16 m ((t) * (v) ^ 2) ((u) * (s) ^ 2))]
  rw [swap_suffix_zero (e_20_16 m ((u) * (s)) ((u) * (s) ^ 2))]
  rw [swap_suffix_zero (e_17_16 m ((t) * (v)) ((u) * (s) ^ 2))]
  rw [swap_suffix (e_23_8 m (v) (t * s))]
  rw [swap_suffix_zero (e_22_8 m (u) (t * s))]
  rw [swap_suffix_zero (e_21_8 m ((t) * (v) ^ 2) (t * s))]
  rw [swap_suffix_zero (e_20_8 m ((u) * (s)) (t * s))]
  rw [swap_suffix_zero (e_17_8 m ((t) * (v)) (t * s))]
  rw [swap_suffix_zero (e_16_8 m ((u) * (s) ^ 2) (t * s))]
  rw [swap_suffix_zero (e_14_8 m (((t) * (v)) * (s)) (t * s))]
  rw [swap_suffix_zero (e_23_14 m (v) ((v) * (t * s)))]
  rw [swap_suffix_zero (e_22_14 m (u) ((v) * (t * s)))]
  rw [swap_suffix_zero (e_21_14 m ((t) * (v) ^ 2) ((v) * (t * s)))]
  rw [swap_suffix_zero (e_20_14 m ((u) * (s)) ((v) * (t * s)))]
  rw [swap_suffix_zero (e_17_14 m ((t) * (v)) ((v) * (t * s)))]
  rw [swap_suffix_zero (e_16_14 m ((u) * (s) ^ 2) ((v) * (t * s)))]
  rw [cancel_suffix (show X m 14 (((t) * (v)) * (s)) * X m 14 ((v) * (t * s)) = 1 by rw [show ((v) * (t * s)) = (((t) * (v)) * (s)) by ring]; exact xx m 14 _)]
  rw [swap_suffix_zero (e_23_16 m (v) (s ^ 2 * u))]
  rw [swap_suffix_zero (e_22_16 m (u) (s ^ 2 * u))]
  rw [swap_suffix_zero (e_21_16 m ((t) * (v) ^ 2) (s ^ 2 * u))]
  rw [swap_suffix_zero (e_20_16 m ((u) * (s)) (s ^ 2 * u))]
  rw [swap_suffix_zero (e_17_16 m ((t) * (v)) (s ^ 2 * u))]
  rw [cancel_suffix (show X m 16 ((u) * (s) ^ 2) * X m 16 (s ^ 2 * u) = 1 by rw [show (s ^ 2 * u) = ((u) * (s) ^ 2) by ring]; exact xx m 16 _)]
  rw [swap_suffix_zero (e_23_17 m (v) (t * v))]
  rw [swap_suffix_zero (e_22_17 m (u) (t * v))]
  rw [swap_suffix_zero (e_21_17 m ((t) * (v) ^ 2) (t * v))]
  rw [swap_suffix_zero (e_20_17 m ((u) * (s)) (t * v))]
  rw [cancel_suffix (show X m 17 ((t) * (v)) * X m 17 (t * v) = 1 by rw [show (t * v) = ((t) * (v)) by ring]; exact xx m 17 _)]
  rw [swap_suffix_zero (e_23_21 m (v) (t * v ^ 2))]
  rw [swap_suffix_zero (e_22_21 m (u) (t * v ^ 2))]
  rw [cancel_suffix (show X m 21 ((t) * (v) ^ 2) * X m 21 (t * v ^ 2) = 1 by rw [show (t * v ^ 2) = ((t) * (v) ^ 2) by ring]; exact xx m 21 _)]
  rw [e_23_20 m (v) (s * u)]
  rw [swap_suffix_zero (e_22_20 m (u) (s * u))]
  rw [cancel_suffix (show X m 20 ((u) * (s)) * X m 20 (s * u) = 1 by rw [show (s * u) = ((u) * (s)) by ring]; exact xx m 20 _)]


end
end ReeF4.CentralCovers.TwoPrimary.TailRelations.BaseIntervals
