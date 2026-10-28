module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus

/-!
# Collection of the two long Ree root-word products

Each equality below is a calculation with actual split root generators.
The two input words are moved past each other using the B₂ and equal-length
matrix exchanges, and correction factors are collected in relative-root order.
Repeated parameters on a split root cancel in characteristic two. The four
scalar variables are independent; the source specialization uses
`s = halfFrobenius m t` and `v = halfFrobenius m u`.

Source: GLS3, Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Theory.AlgebraicGroup StandardRootSystem
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators
noncomputable section

private theorem swap_suffix {G : Type*} [Group G] {a b c : G}
    (h : a * b = b * a * c) (d : G) : a * (b * d) = b * (a * (c * d)) := by
  simpa only [mul_assoc] using congrArg (fun z => z * d) h

private theorem swap_suffix_two {G : Type*} [Group G] {a b c d : G}
    (h : a * b = b * a * c * d) (e : G) :
    a * (b * e) = b * (a * (c * (d * e))) := by
  simpa only [mul_assoc] using congrArg (fun z => z * e) h

private theorem cancel_suffix {G : Type*} [Group G] {a : G}
    (h : a * a = 1) (b : G) : a * (a * b) = b := by
  rw [← mul_assoc, h, one_mul]

private theorem reverse_two {G : Type*} [Group G] {a b c d : G}
    (h : b * a = a * b * c * d) (hc : c * c = 1) (hd : d * d = 1)
    (hcd : Commute c d) : a * b = b * a * c * d := by
  have hcc : (c * d) * (c * d) = 1 := by
    rw [hcd.symm.mul_mul_mul_comm, hc, hd, one_mul]
  calc
    a * b = (a * b * (c * d)) * (c * d) := by rw [mul_assoc, hcc, mul_one]
    _ = b * a * c * d := by
      simpa only [mul_assoc] using congrArg (fun z => z * (c * d)) h.symm

attribute [local irreducible] X

private theorem c_0_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 0 a) (X m 18 b) :=
  xc m 0 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_0_19 (m : ℕ) (a b : CoefficientField m) :
    X m 0 a * X m 19 b = X m 19 b * X m 0 a * X m 7 (a * b) * X m 12 (a * b ^ 2) := by
  exact reverse_two (xb m 0 19 7 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 7 (a * b)) (xx m 12 (a * b ^ 2))
    (xc m 7 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * b) (a * b ^ 2))

private theorem c_0_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 0 a) (X m 20 b) :=
  xc m 0 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_0_22 (m : ℕ) (a b : CoefficientField m) :
    X m 0 a * X m 22 b = X m 22 b * X m 0 a * X m 18 (a * b) := by
  exact xs m 0 22 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_0_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 0 a) (X m 23 b) :=
  xc m 0 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_1_18 (m : ℕ) (a b : CoefficientField m) :
    X m 1 a * X m 18 b = X m 18 b * X m 1 a * X m 13 (a * b) * X m 6 (b * a ^ 2) := by
  simpa only [mul_comm a b] using xb m 18 1 13 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_1_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 1 a) (X m 19 b) :=
  xc m 1 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_1_20 (m : ℕ) (a b : CoefficientField m) :
    X m 1 a * X m 20 b = X m 20 b * X m 1 a * X m 17 (a * b) := by
  exact xs m 1 20 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_1_22 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 1 a) (X m 22 b) :=
  xc m 1 22 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_1_23 (m : ℕ) (a b : CoefficientField m) :
    X m 1 a * X m 23 b = X m 23 b * X m 1 a * X m 19 (a * b) := by
  exact xs m 1 23 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_2_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 2 a) (X m 18 b) :=
  xc m 2 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_2_19 (m : ℕ) (a b : CoefficientField m) :
    X m 2 a * X m 19 b = X m 19 b * X m 2 a * X m 5 (a * b) := by
  exact xs m 2 19 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_2_20 (m : ℕ) (a b : CoefficientField m) :
    X m 2 a * X m 20 b = X m 20 b * X m 2 a * X m 11 (a * b) := by
  exact xs m 2 20 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_2_22 (m : ℕ) (a b : CoefficientField m) :
    X m 2 a * X m 22 b = X m 22 b * X m 2 a * X m 13 (a * b) * X m 4 (b * a ^ 2) := by
  simpa only [mul_comm a b] using xb m 22 2 13 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem s_2_23 (m : ℕ) (a b : CoefficientField m) :
    X m 2 a * X m 23 b = X m 23 b * X m 2 a * X m 7 (a * b) := by
  exact xs m 2 23 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_4_23 (m : ℕ) (a b : CoefficientField m) :
    X m 4 a * X m 23 b = X m 23 b * X m 4 a * X m 11 (a * b) * X m 16 (a * b ^ 2) := by
  exact reverse_two (xb m 4 23 11 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 11 (a * b)) (xx m 16 (a * b ^ 2))
    (xc m 11 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * b) (a * b ^ 2))

private theorem c_5_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 5 a) (X m 2 b) :=
  xc m 5 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_5_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 5 a) (X m 4 b) :=
  xc m 5 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 2 b) :=
  xc m 6 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 4 b) :=
  xc m 6 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_19 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 19 b) :=
  xc m 6 19 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_6_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 6 a) (X m 20 b) :=
  xc m 6 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_6_23 (m : ℕ) (a b : CoefficientField m) :
    X m 6 a * X m 23 b = X m 23 b * X m 6 a * X m 17 (a * b) * X m 21 (a * b ^ 2) := by
  exact reverse_two (xb m 6 23 17 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 17 (a * b)) (xx m 21 (a * b ^ 2))
    (xc m 17 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * b) (a * b ^ 2))

private theorem s_7_1 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 1 b = X m 1 b * X m 7 a * X m 5 (a * b) := by
  exact xs m 7 1 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_7_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 2 b) :=
  xc m 7 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 4 b) :=
  xc m 7 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_7_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 5 b) :=
  xc m 7 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_7_6 (m : ℕ) (a b : CoefficientField m) :
    X m 7 a * X m 6 b = X m 6 b * X m 7 a * X m 8 (a * b) * X m 9 (b * a ^ 2) := by
  simpa only [mul_comm a b] using xb m 6 7 8 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_7_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 7 a) (X m 20 b) :=
  xc m 7 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 6 b) :=
  xc m 8 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_7 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 7 b) :=
  xc m 8 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_8_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 8 a) (X m 20 b) :=
  xc m 8 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_8 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 8 b) :=
  xc m 9 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_9_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 9 a) (X m 20 b) :=
  xc m 9 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_10_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 6 b) :=
  xc m 10 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_10_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 10 a) (X m 20 b) :=
  xc m 10 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 6 b) :=
  xc m 11 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_7 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 7 b) :=
  xc m 11 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_8 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 8 b) :=
  xc m 11 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_9 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 9 b) :=
  xc m 11 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_11_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 11 a) (X m 10 b) :=
  xc m 11 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_1 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 1 b) :=
  xc m 12 1 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 2 b) :=
  xc m 12 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 5 b) :=
  xc m 12 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_12_6 (m : ℕ) (a b : CoefficientField m) :
    X m 12 a * X m 6 b = X m 6 b * X m 12 a * X m 10 (a * b) := by
  exact xs m 12 6 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_12_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 10 b) :=
  xc m 12 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_12_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 12 a) (X m 20 b) :=
  xc m 12 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 2 b) :=
  xc m 13 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_13_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 6 b) :=
  xc m 13 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_13_19 (m : ℕ) (a b : CoefficientField m) :
    X m 13 a * X m 19 b = X m 19 b * X m 13 a * X m 17 (a * b) := by
  exact xs m 13 19 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_13_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 13 a) (X m 20 b) :=
  xc m 13 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 6 b) :=
  xc m 14 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_8 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 8 b) :=
  xc m 14 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_9 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 9 b) :=
  xc m 14 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 10 b) :=
  xc m 14 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 12 b) :=
  xc m 14 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_14_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 14 a) (X m 13 b) :=
  xc m 14 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_15_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 15 a) (X m 14 b) :=
  xc m 15 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_16_6 (m : ℕ) (a b : CoefficientField m) :
    X m 16 a * X m 6 b = X m 6 b * X m 16 a * X m 15 (a * b) := by
  exact xs m 16 6 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_16_15 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 16 a) (X m 15 b) :=
  xc m 16 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_17_2 (m : ℕ) (a b : CoefficientField m) :
    X m 17 a * X m 2 b = X m 2 b * X m 17 a * X m 8 (a * b) := by
  exact xs m 17 2 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_17_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 6 b) :=
  xc m 17 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_17_7 (m : ℕ) (a b : CoefficientField m) :
    X m 17 a * X m 7 b = X m 7 b * X m 17 a * X m 14 (a * b) := by
  exact xs m 17 7 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_17_8 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 8 b) :=
  xc m 17 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_9 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 9 b) :=
  xc m 17 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 10 b) :=
  xc m 17 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_11 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 11 b) :=
  xc m 17 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_12 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 12 b) :=
  xc m 17 12 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 13 b) :=
  xc m 17 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 14 b) :=
  xc m 17 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_17_20 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 17 a) (X m 20 b) :=
  xc m 17 20 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_18_1 (m : ℕ) (a b : CoefficientField m) :
    X m 18 a * X m 1 b = X m 1 b * X m 18 a * X m 13 (a * b) * X m 6 (a * b ^ 2) := by
  exact reverse_two (xb m 18 1 13 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 13 (a * b)) (xx m 6 (a * b ^ 2))
    (xc m 13 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a * b) (a * b ^ 2))

private theorem c_18_2 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 2 b) :=
  xc m 18 2 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_18_4 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 4 b) :=
  xc m 18 4 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_18_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 6 b) :=
  xc m 18 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_18_13 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 13 b) :=
  xc m 18 13 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_18_23 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 18 a) (X m 23 b) :=
  xc m 18 23 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_19_2 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 2 b = X m 2 b * X m 19 a * X m 5 (a * b) := by
  exact xs m 19 2 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_19_4 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 4 b = X m 4 b * X m 19 a * X m 8 (a * b) * X m 10 (b * a ^ 2) := by
  simpa only [mul_comm a b] using xb m 4 19 8 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_19_5 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 5 b) :=
  xc m 19 5 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_6 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 6 b) :=
  xc m 19 6 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_7 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 7 b) :=
  xc m 19 7 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_8 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 8 b) :=
  xc m 19 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_10 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 10 b) :=
  xc m 19 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_19_11 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 11 b = X m 11 b * X m 19 a * X m 14 (a * b) := by
  exact xs m 19 11 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem c_19_14 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 14 b) :=
  xc m 19 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_16 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 16 b) :=
  xc m 19 16 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem c_19_17 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 19 a) (X m 17 b) :=
  xc m 19 17 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem s_19_18 (m : ℕ) (a b : CoefficientField m) :
    X m 19 a * X m 18 b = X m 18 b * X m 19 a * X m 20 (a * b) * X m 21 (b * a ^ 2) := by
  simpa only [mul_comm a b] using xb m 18 19 20 21 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem c_21_18 (m : ℕ) (a b : CoefficientField m) :
    Commute (X m 21 a) (X m 18 b) :=
  xc m 21 18 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) a b

private theorem first_eighth_move (m : ℕ) (t s u v : CoefficientField m) :
    X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 22 (u) * (X m 23 (v) * 1)))) =
      X m 22 (u) * (X m 23 (v) * (X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 19 (s * v) * (X m 5 (t * s ^ 2 * v) * (X m 7 (t * s * v) * (X m 4 (t ^ 2 * s ^ 2 * u) * (X m 11 (t ^ 2 * s ^ 2 * u * v) * (X m 16 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 6 (t * s ^ 2 * u) * (X m 17 (t * s ^ 2 * u * v) * (X m 21 (t * s ^ 2 * u * v ^ 2) * (X m 18 (t * u) * 1)))))))))))))) := by
  have h0 : X m 2 (t * s) * X m 22 (u) =
      X m 22 (u) * X m 2 (t * s) * X m 13 (t * s * u) * X m 4 (t ^ 2 * s ^ 2 * u) := by
    have hh := s_2_22 m (t * s) (u)
    rw [show (t * s) * (u) = t * s * u by ring, show (u) * (t * s) ^ 2 = t ^ 2 * s ^ 2 * u by ring] at hh
    exact hh
  rw [swap_suffix_two h0]
  rw [(c_1_22 m (s) (u)).left_comm]
  have h2 : X m 0 (t) * X m 22 (u) =
      X m 22 (u) * X m 0 (t) * X m 18 (t * u) := by
    have hh := s_0_22 m (t) (u)
    rw [show (t) * (u) = t * u by ring] at hh
    exact hh
  rw [swap_suffix h2]
  have h3 : X m 18 (t * u) * X m 1 (s) =
      X m 1 (s) * X m 18 (t * u) * X m 13 (t * s * u) * X m 6 (t * s ^ 2 * u) := by
    have hh := s_18_1 m (t * u) (s)
    rw [show (t * u) * (s) = t * s * u by ring, show (t * u) * (s) ^ 2 = t * s ^ 2 * u by ring] at hh
    exact hh
  rw [swap_suffix_two h3]
  rw [(c_18_13 m (t * u) (t * s * u)).left_comm]
  rw [(c_18_6 m (t * u) (t * s ^ 2 * u)).left_comm]
  rw [(c_13_6 m (t * s * u) (t * s ^ 2 * u)).left_comm]
  rw [(c_18_2 m (t * u) (t * s)).left_comm]
  rw [(c_13_2 m (t * s * u) (t * s)).left_comm]
  rw [(c_6_2 m (t * s ^ 2 * u) (t * s)).left_comm]
  rw [(c_18_13 m (t * u) (t * s * u)).left_comm]
  rw [cancel_suffix (xx m 13 (t * s * u))]
  rw [(c_18_4 m (t * u) (t ^ 2 * s ^ 2 * u)).left_comm]
  rw [(c_6_4 m (t * s ^ 2 * u) (t ^ 2 * s ^ 2 * u)).left_comm]
  rw [(c_18_23 m (t * u) (v)).left_comm]
  have h15 : X m 6 (t * s ^ 2 * u) * X m 23 (v) =
      X m 23 (v) * X m 6 (t * s ^ 2 * u) * X m 17 (t * s ^ 2 * u * v) * X m 21 (t * s ^ 2 * u * v ^ 2) := by
    have hh := s_6_23 m (t * s ^ 2 * u) (v)
    rw [show (t * s ^ 2 * u) * (v) = t * s ^ 2 * u * v by ring, show (t * s ^ 2 * u) * (v) ^ 2 = t * s ^ 2 * u * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix_two h15]
  have h16 : X m 4 (t ^ 2 * s ^ 2 * u) * X m 23 (v) =
      X m 23 (v) * X m 4 (t ^ 2 * s ^ 2 * u) * X m 11 (t ^ 2 * s ^ 2 * u * v) * X m 16 (t ^ 2 * s ^ 2 * u * v ^ 2) := by
    have hh := s_4_23 m (t ^ 2 * s ^ 2 * u) (v)
    rw [show (t ^ 2 * s ^ 2 * u) * (v) = t ^ 2 * s ^ 2 * u * v by ring, show (t ^ 2 * s ^ 2 * u) * (v) ^ 2 = t ^ 2 * s ^ 2 * u * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix_two h16]
  have h17 : X m 2 (t * s) * X m 23 (v) =
      X m 23 (v) * X m 2 (t * s) * X m 7 (t * s * v) := by
    have hh := s_2_23 m (t * s) (v)
    rw [show (t * s) * (v) = t * s * v by ring] at hh
    exact hh
  rw [swap_suffix h17]
  have h18 : X m 1 (s) * X m 23 (v) =
      X m 23 (v) * X m 1 (s) * X m 19 (s * v) := by
    have hh := s_1_23 m (s) (v)
    rw [show (s) * (v) = s * v by ring] at hh
    exact hh
  rw [swap_suffix h18]
  rw [(c_0_23 m (t) (v)).left_comm]
  have h20 : X m 19 (s * v) * X m 2 (t * s) =
      X m 2 (t * s) * X m 19 (s * v) * X m 5 (t * s ^ 2 * v) := by
    have hh := s_19_2 m (s * v) (t * s)
    rw [show (s * v) * (t * s) = t * s ^ 2 * v by ring] at hh
    exact hh
  rw [swap_suffix h20]

private theorem first_eighth_corrections (m : ℕ) (t s u v : CoefficientField m) :
    X m 19 (s * v) * (X m 5 (t * s ^ 2 * v) * (X m 7 (t * s * v) * (X m 4 (t ^ 2 * s ^ 2 * u) * (X m 11 (t ^ 2 * s ^ 2 * u * v) * (X m 16 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 6 (t * s ^ 2 * u) * (X m 17 (t * s ^ 2 * u * v) * (X m 21 (t * s ^ 2 * u * v ^ 2) * (X m 18 (t * u) * 1))))))))) =
      X m 4 (t ^ 2 * s ^ 2 * u) * (X m 5 (t * s ^ 2 * v) * (X m 6 (t * s ^ 2 * u) * (X m 7 (t * s * v) * (X m 9 (t ^ 3 * s ^ 4 * u * v ^ 2) * (X m 10 (t ^ 2 * s ^ 4 * u * v ^ 2) * (X m 11 (t ^ 2 * s ^ 2 * u * v) * (X m 14 (t ^ 2 * s ^ 3 * u * v ^ 2) * (X m 15 (t ^ 3 * s ^ 4 * u ^ 2 * v ^ 2) * (X m 16 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 17 (t * s ^ 2 * u * v) * (X m 18 (t * u) * (X m 19 (s * v) * (X m 20 (t * s * u * v) * 1))))))))))))) := by
  rw [(c_19_5 m (s * v) (t * s ^ 2 * v)).left_comm]
  rw [(c_19_7 m (s * v) (t * s * v)).left_comm]
  have h2 : X m 19 (s * v) * X m 4 (t ^ 2 * s ^ 2 * u) =
      X m 4 (t ^ 2 * s ^ 2 * u) * X m 19 (s * v) * X m 8 (t ^ 2 * s ^ 3 * u * v) * X m 10 (t ^ 2 * s ^ 4 * u * v ^ 2) := by
    have hh := s_19_4 m (s * v) (t ^ 2 * s ^ 2 * u)
    rw [show (s * v) * (t ^ 2 * s ^ 2 * u) = t ^ 2 * s ^ 3 * u * v by ring, show (t ^ 2 * s ^ 2 * u) * (s * v) ^ 2 = t ^ 2 * s ^ 4 * u * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix_two h2]
  rw [(c_7_4 m (t * s * v) (t ^ 2 * s ^ 2 * u)).left_comm]
  rw [(c_5_4 m (t * s ^ 2 * v) (t ^ 2 * s ^ 2 * u)).left_comm]
  rw [(c_19_8 m (s * v) (t ^ 2 * s ^ 3 * u * v)).left_comm]
  rw [(c_19_10 m (s * v) (t ^ 2 * s ^ 4 * u * v ^ 2)).left_comm]
  have h7 : X m 19 (s * v) * X m 11 (t ^ 2 * s ^ 2 * u * v) =
      X m 11 (t ^ 2 * s ^ 2 * u * v) * X m 19 (s * v) * X m 14 (t ^ 2 * s ^ 3 * u * v ^ 2) := by
    have hh := s_19_11 m (s * v) (t ^ 2 * s ^ 2 * u * v)
    rw [show (s * v) * (t ^ 2 * s ^ 2 * u * v) = t ^ 2 * s ^ 3 * u * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix h7]
  rw [(c_19_14 m (s * v) (t ^ 2 * s ^ 3 * u * v ^ 2)).left_comm]
  rw [(c_19_16 m (s * v) (t ^ 2 * s ^ 2 * u * v ^ 2)).left_comm]
  rw [(c_19_6 m (s * v) (t * s ^ 2 * u)).left_comm]
  have h11 : X m 16 (t ^ 2 * s ^ 2 * u * v ^ 2) * X m 6 (t * s ^ 2 * u) =
      X m 6 (t * s ^ 2 * u) * X m 16 (t ^ 2 * s ^ 2 * u * v ^ 2) * X m 15 (t ^ 3 * s ^ 4 * u ^ 2 * v ^ 2) := by
    have hh := s_16_6 m (t ^ 2 * s ^ 2 * u * v ^ 2) (t * s ^ 2 * u)
    rw [show (t ^ 2 * s ^ 2 * u * v ^ 2) * (t * s ^ 2 * u) = t ^ 3 * s ^ 4 * u ^ 2 * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix h11]
  rw [(c_14_6 m (t ^ 2 * s ^ 3 * u * v ^ 2) (t * s ^ 2 * u)).left_comm]
  rw [(c_11_6 m (t ^ 2 * s ^ 2 * u * v) (t * s ^ 2 * u)).left_comm]
  rw [(c_10_6 m (t ^ 2 * s ^ 4 * u * v ^ 2) (t * s ^ 2 * u)).left_comm]
  rw [(c_8_6 m (t ^ 2 * s ^ 3 * u * v) (t * s ^ 2 * u)).left_comm]
  have h16 : X m 7 (t * s * v) * X m 6 (t * s ^ 2 * u) =
      X m 6 (t * s ^ 2 * u) * X m 7 (t * s * v) * X m 8 (t ^ 2 * s ^ 3 * u * v) * X m 9 (t ^ 3 * s ^ 4 * u * v ^ 2) := by
    have hh := s_7_6 m (t * s * v) (t * s ^ 2 * u)
    rw [show (t * s * v) * (t * s ^ 2 * u) = t ^ 2 * s ^ 3 * u * v by ring, show (t * s ^ 2 * u) * (t * s * v) ^ 2 = t ^ 3 * s ^ 4 * u * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix_two h16]
  rw [(c_9_8 m (t ^ 3 * s ^ 4 * u * v ^ 2) (t ^ 2 * s ^ 3 * u * v)).left_comm]
  rw [cancel_suffix (xx m 8 (t ^ 2 * s ^ 3 * u * v))]
  rw [(c_16_15 m (t ^ 2 * s ^ 2 * u * v ^ 2) (t ^ 3 * s ^ 4 * u ^ 2 * v ^ 2)).left_comm]
  rw [(c_19_17 m (s * v) (t * s ^ 2 * u * v)).left_comm]
  rw [(c_21_18 m (t * s ^ 2 * u * v ^ 2) (t * u)).left_comm]
  have h22 : X m 19 (s * v) * X m 18 (t * u) =
      X m 18 (t * u) * X m 19 (s * v) * X m 20 (t * s * u * v) * X m 21 (t * s ^ 2 * u * v ^ 2) := by
    have hh := s_19_18 m (s * v) (t * u)
    rw [show (s * v) * (t * u) = t * s * u * v by ring, show (t * u) * (s * v) ^ 2 = t * s ^ 2 * u * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix_two h22]
  rw [cancel_suffix (xx m 21 (t * s ^ 2 * u * v ^ 2))]

private theorem first_eighth_right (m : ℕ) (t s u v : CoefficientField m) :
    X m 22 (u) * (X m 23 (v) * (X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 4 (t ^ 2 * s ^ 2 * u) * (X m 5 (t * s ^ 2 * v) * (X m 8 (t ^ 2 * s ^ 3 * u * v) * (X m 7 (t * s * v) * (X m 6 (t * s ^ 2 * u) * (X m 10 (t ^ 2 * s ^ 4 * u * v ^ 2) * (X m 11 (t ^ 2 * s ^ 2 * u * v) * (X m 15 (t ^ 3 * s ^ 4 * u ^ 2 * v ^ 2) * (X m 14 (t ^ 2 * s ^ 3 * u * v ^ 2) * (X m 16 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 17 (t * s ^ 2 * u * v) * (X m 18 (t * u) * (X m 19 (s * v) * (X m 20 (t * s * u * v) * 1)))))))))))))))))) =
      X m 22 (u) * (X m 23 (v) * (X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 4 (t ^ 2 * s ^ 2 * u) * (X m 5 (t * s ^ 2 * v) * (X m 6 (t * s ^ 2 * u) * (X m 7 (t * s * v) * (X m 9 (t ^ 3 * s ^ 4 * u * v ^ 2) * (X m 10 (t ^ 2 * s ^ 4 * u * v ^ 2) * (X m 11 (t ^ 2 * s ^ 2 * u * v) * (X m 14 (t ^ 2 * s ^ 3 * u * v ^ 2) * (X m 15 (t ^ 3 * s ^ 4 * u ^ 2 * v ^ 2) * (X m 16 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 17 (t * s ^ 2 * u * v) * (X m 18 (t * u) * (X m 19 (s * v) * (X m 20 (t * s * u * v) * 1)))))))))))))))))) := by
  rw [(c_8_7 m (t ^ 2 * s ^ 3 * u * v) (t * s * v)).left_comm]
  rw [(c_8_6 m (t ^ 2 * s ^ 3 * u * v) (t * s ^ 2 * u)).left_comm]
  have h2 : X m 7 (t * s * v) * X m 6 (t * s ^ 2 * u) =
      X m 6 (t * s ^ 2 * u) * X m 7 (t * s * v) * X m 8 (t ^ 2 * s ^ 3 * u * v) * X m 9 (t ^ 3 * s ^ 4 * u * v ^ 2) := by
    have hh := s_7_6 m (t * s * v) (t * s ^ 2 * u)
    rw [show (t * s * v) * (t * s ^ 2 * u) = t ^ 2 * s ^ 3 * u * v by ring, show (t * s ^ 2 * u) * (t * s * v) ^ 2 = t ^ 3 * s ^ 4 * u * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix_two h2]
  rw [(c_9_8 m (t ^ 3 * s ^ 4 * u * v ^ 2) (t ^ 2 * s ^ 3 * u * v)).left_comm]
  rw [cancel_suffix (xx m 8 (t ^ 2 * s ^ 3 * u * v))]
  rw [(c_15_14 m (t ^ 3 * s ^ 4 * u ^ 2 * v ^ 2) (t ^ 2 * s ^ 3 * u * v ^ 2)).left_comm]

private theorem first_eighth_left (m : ℕ) (t s u v : CoefficientField m) :
    X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 22 (u) * (X m 23 (v) * 1)))) =
      X m 22 (u) * (X m 23 (v) * (X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 4 (t ^ 2 * s ^ 2 * u) * (X m 5 (t * s ^ 2 * v) * (X m 6 (t * s ^ 2 * u) * (X m 7 (t * s * v) * (X m 9 (t ^ 3 * s ^ 4 * u * v ^ 2) * (X m 10 (t ^ 2 * s ^ 4 * u * v ^ 2) * (X m 11 (t ^ 2 * s ^ 2 * u * v) * (X m 14 (t ^ 2 * s ^ 3 * u * v ^ 2) * (X m 15 (t ^ 3 * s ^ 4 * u ^ 2 * v ^ 2) * (X m 16 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 17 (t * s ^ 2 * u * v) * (X m 18 (t * u) * (X m 19 (s * v) * (X m 20 (t * s * u * v) * 1)))))))))))))))))) := by
  calc
    _ = X m 22 (u) * (X m 23 (v) * (X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 19 (s * v) * (X m 5 (t * s ^ 2 * v) * (X m 7 (t * s * v) * (X m 4 (t ^ 2 * s ^ 2 * u) * (X m 11 (t ^ 2 * s ^ 2 * u * v) * (X m 16 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 6 (t * s ^ 2 * u) * (X m 17 (t * s ^ 2 * u * v) * (X m 21 (t * s ^ 2 * u * v ^ 2) * (X m 18 (t * u) * 1)))))))))))))) := first_eighth_move m t s u v
    _ = _ := by
      simpa only [mul_assoc] using
        congrArg (fun z => (X m 22 (u) * X m 23 (v) * X m 0 (t) * X m 1 (s) * X m 2 (t * s)) * z) (first_eighth_corrections m t s u v)

/-- Exact collected split-word exchange for the first-eighth pair. -/
theorem collect_first_eighth (m : ℕ) (t s u v : CoefficientField m) :
    X m 0 (t) * X m 1 (s) * X m 2 (t * s) * X m 22 (u) * X m 23 (v) =
      X m 22 (u) * X m 23 (v) * X m 0 (t) * X m 1 (s) * X m 2 (t * s) * X m 4 (t ^ 2 * s ^ 2 * u) * X m 5 (t * s ^ 2 * v) * X m 8 (t ^ 2 * s ^ 3 * u * v) * X m 7 (t * s * v) * X m 6 (t * s ^ 2 * u) * X m 10 (t ^ 2 * s ^ 4 * u * v ^ 2) * X m 11 (t ^ 2 * s ^ 2 * u * v) * X m 15 (t ^ 3 * s ^ 4 * u ^ 2 * v ^ 2) * X m 14 (t ^ 2 * s ^ 3 * u * v ^ 2) * X m 16 (t ^ 2 * s ^ 2 * u * v ^ 2) * X m 17 (t * s ^ 2 * u * v) * X m 18 (t * u) * X m 19 (s * v) * X m 20 (t * s * u * v) := by
  simpa only [mul_one, mul_assoc] using
    (first_eighth_left m t s u v).trans (first_eighth_right m t s u v).symm

private theorem first_seventh_move (m : ℕ) (t s u v : CoefficientField m) :
    X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 18 (u) * (X m 19 (v) * (X m 20 (u * v) * 1))))) =
      X m 18 (u) * (X m 19 (v) * (X m 20 (u * v) * (X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 17 (s * u * v) * (X m 8 (t * s ^ 2 * u * v) * (X m 11 (t * s * u * v) * (X m 6 (s ^ 2 * u) * (X m 7 (t * v) * (X m 8 (t * s ^ 2 * u * v) * (X m 9 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 10 (t * s ^ 2 * u * v ^ 2) * (X m 12 (t * v ^ 2) * (X m 13 (s * u) * (X m 17 (s * u * v) * 1)))))))))))))))) := by
  rw [(c_2_18 m (t * s) (u)).left_comm]
  have h1 : X m 1 (s) * X m 18 (u) =
      X m 18 (u) * X m 1 (s) * X m 13 (s * u) * X m 6 (s ^ 2 * u) := by
    have hh := s_1_18 m (s) (u)
    rw [show (s) * (u) = s * u by ring, show (u) * (s) ^ 2 = s ^ 2 * u by ring] at hh
    exact hh
  rw [swap_suffix_two h1]
  rw [(c_0_18 m (t) (u)).left_comm]
  rw [(c_13_6 m (s * u) (s ^ 2 * u)).left_comm]
  rw [(c_13_2 m (s * u) (t * s)).left_comm]
  rw [(c_6_2 m (s ^ 2 * u) (t * s)).left_comm]
  have h6 : X m 13 (s * u) * X m 19 (v) =
      X m 19 (v) * X m 13 (s * u) * X m 17 (s * u * v) := by
    have hh := s_13_19 m (s * u) (v)
    rw [show (s * u) * (v) = s * u * v by ring] at hh
    exact hh
  rw [swap_suffix h6]
  rw [(c_6_19 m (s ^ 2 * u) (v)).left_comm]
  have h8 : X m 2 (t * s) * X m 19 (v) =
      X m 19 (v) * X m 2 (t * s) * X m 5 (t * s * v) := by
    have hh := s_2_19 m (t * s) (v)
    rw [show (t * s) * (v) = t * s * v by ring] at hh
    exact hh
  rw [swap_suffix h8]
  rw [(c_1_19 m (s) (v)).left_comm]
  have h10 : X m 0 (t) * X m 19 (v) =
      X m 19 (v) * X m 0 (t) * X m 7 (t * v) * X m 12 (t * v ^ 2) := by
    have hh := s_0_19 m (t) (v)
    rw [show (t) * (v) = t * v by ring, show (t) * (v) ^ 2 = t * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix_two h10]
  rw [(c_12_1 m (t * v ^ 2) (s)).left_comm]
  have h12 : X m 7 (t * v) * X m 1 (s) =
      X m 1 (s) * X m 7 (t * v) * X m 5 (t * s * v) := by
    have hh := s_7_1 m (t * v) (s)
    rw [show (t * v) * (s) = t * s * v by ring] at hh
    exact hh
  rw [swap_suffix h12]
  rw [(c_7_5 m (t * v) (t * s * v)).left_comm]
  rw [(c_12_2 m (t * v ^ 2) (t * s)).left_comm]
  rw [(c_7_2 m (t * v) (t * s)).left_comm]
  rw [(c_5_2 m (t * s * v) (t * s)).left_comm]
  rw [(c_12_5 m (t * v ^ 2) (t * s * v)).left_comm]
  rw [(c_7_5 m (t * v) (t * s * v)).left_comm]
  rw [cancel_suffix (xx m 5 (t * s * v))]
  have h20 : X m 12 (t * v ^ 2) * X m 6 (s ^ 2 * u) =
      X m 6 (s ^ 2 * u) * X m 12 (t * v ^ 2) * X m 10 (t * s ^ 2 * u * v ^ 2) := by
    have hh := s_12_6 m (t * v ^ 2) (s ^ 2 * u)
    rw [show (t * v ^ 2) * (s ^ 2 * u) = t * s ^ 2 * u * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix h20]
  have h21 : X m 7 (t * v) * X m 6 (s ^ 2 * u) =
      X m 6 (s ^ 2 * u) * X m 7 (t * v) * X m 8 (t * s ^ 2 * u * v) * X m 9 (t ^ 2 * s ^ 2 * u * v ^ 2) := by
    have hh := s_7_6 m (t * v) (s ^ 2 * u)
    rw [show (t * v) * (s ^ 2 * u) = t * s ^ 2 * u * v by ring, show (s ^ 2 * u) * (t * v) ^ 2 = t ^ 2 * s ^ 2 * u * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix_two h21]
  rw [(c_12_10 m (t * v ^ 2) (t * s ^ 2 * u * v ^ 2)).left_comm]
  rw [(c_17_20 m (s * u * v) (u * v)).left_comm]
  rw [(c_13_20 m (s * u) (u * v)).left_comm]
  rw [(c_12_20 m (t * v ^ 2) (u * v)).left_comm]
  rw [(c_10_20 m (t * s ^ 2 * u * v ^ 2) (u * v)).left_comm]
  rw [(c_9_20 m (t ^ 2 * s ^ 2 * u * v ^ 2) (u * v)).left_comm]
  rw [(c_8_20 m (t * s ^ 2 * u * v) (u * v)).left_comm]
  rw [(c_7_20 m (t * v) (u * v)).left_comm]
  rw [(c_6_20 m (s ^ 2 * u) (u * v)).left_comm]
  have h31 : X m 2 (t * s) * X m 20 (u * v) =
      X m 20 (u * v) * X m 2 (t * s) * X m 11 (t * s * u * v) := by
    have hh := s_2_20 m (t * s) (u * v)
    rw [show (t * s) * (u * v) = t * s * u * v by ring] at hh
    exact hh
  rw [swap_suffix h31]
  have h32 : X m 1 (s) * X m 20 (u * v) =
      X m 20 (u * v) * X m 1 (s) * X m 17 (s * u * v) := by
    have hh := s_1_20 m (s) (u * v)
    rw [show (s) * (u * v) = s * u * v by ring] at hh
    exact hh
  rw [swap_suffix h32]
  rw [(c_0_20 m (t) (u * v)).left_comm]
  have h34 : X m 17 (s * u * v) * X m 2 (t * s) =
      X m 2 (t * s) * X m 17 (s * u * v) * X m 8 (t * s ^ 2 * u * v) := by
    have hh := s_17_2 m (s * u * v) (t * s)
    rw [show (s * u * v) * (t * s) = t * s ^ 2 * u * v by ring] at hh
    exact hh
  rw [swap_suffix h34]

private theorem first_seventh_corrections (m : ℕ) (t s u v : CoefficientField m) :
    X m 17 (s * u * v) * (X m 8 (t * s ^ 2 * u * v) * (X m 11 (t * s * u * v) * (X m 6 (s ^ 2 * u) * (X m 7 (t * v) * (X m 8 (t * s ^ 2 * u * v) * (X m 9 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 10 (t * s ^ 2 * u * v ^ 2) * (X m 12 (t * v ^ 2) * (X m 13 (s * u) * (X m 17 (s * u * v) * 1)))))))))) =
      X m 6 (s ^ 2 * u) * (X m 7 (t * v) * (X m 9 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 10 (t * s ^ 2 * u * v ^ 2) * (X m 11 (t * s * u * v) * (X m 12 (t * v ^ 2) * (X m 13 (s * u) * (X m 14 (t * s * u * v ^ 2) * 1))))))) := by
  rw [(c_17_8 m (s * u * v) (t * s ^ 2 * u * v)).left_comm]
  rw [(c_17_11 m (s * u * v) (t * s * u * v)).left_comm]
  rw [(c_17_6 m (s * u * v) (s ^ 2 * u)).left_comm]
  rw [(c_11_6 m (t * s * u * v) (s ^ 2 * u)).left_comm]
  rw [(c_8_6 m (t * s ^ 2 * u * v) (s ^ 2 * u)).left_comm]
  have h5 : X m 17 (s * u * v) * X m 7 (t * v) =
      X m 7 (t * v) * X m 17 (s * u * v) * X m 14 (t * s * u * v ^ 2) := by
    have hh := s_17_7 m (s * u * v) (t * v)
    rw [show (s * u * v) * (t * v) = t * s * u * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix h5]
  rw [(c_11_7 m (t * s * u * v) (t * v)).left_comm]
  rw [(c_8_7 m (t * s ^ 2 * u * v) (t * v)).left_comm]
  rw [(c_17_14 m (s * u * v) (t * s * u * v ^ 2)).left_comm]
  rw [(c_17_8 m (s * u * v) (t * s ^ 2 * u * v)).left_comm]
  rw [(c_14_8 m (t * s * u * v ^ 2) (t * s ^ 2 * u * v)).left_comm]
  rw [(c_11_8 m (t * s * u * v) (t * s ^ 2 * u * v)).left_comm]
  rw [cancel_suffix (xx m 8 (t * s ^ 2 * u * v))]
  rw [(c_17_9 m (s * u * v) (t ^ 2 * s ^ 2 * u * v ^ 2)).left_comm]
  rw [(c_14_9 m (t * s * u * v ^ 2) (t ^ 2 * s ^ 2 * u * v ^ 2)).left_comm]
  rw [(c_11_9 m (t * s * u * v) (t ^ 2 * s ^ 2 * u * v ^ 2)).left_comm]
  rw [(c_17_10 m (s * u * v) (t * s ^ 2 * u * v ^ 2)).left_comm]
  rw [(c_14_10 m (t * s * u * v ^ 2) (t * s ^ 2 * u * v ^ 2)).left_comm]
  rw [(c_11_10 m (t * s * u * v) (t * s ^ 2 * u * v ^ 2)).left_comm]
  rw [(c_17_12 m (s * u * v) (t * v ^ 2)).left_comm]
  rw [(c_14_12 m (t * s * u * v ^ 2) (t * v ^ 2)).left_comm]
  rw [(c_17_13 m (s * u * v) (s * u)).left_comm]
  rw [(c_14_13 m (t * s * u * v ^ 2) (s * u)).left_comm]
  rw [cancel_suffix (xx m 17 (s * u * v))]

private theorem first_seventh_right (m : ℕ) (t s u v : CoefficientField m) :
    X m 18 (u) * (X m 19 (v) * (X m 20 (u * v) * (X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 8 (t * s ^ 2 * u * v) * (X m 7 (t * v) * (X m 6 (s ^ 2 * u) * (X m 10 (t * s ^ 2 * u * v ^ 2) * (X m 11 (t * s * u * v) * (X m 12 (t * v ^ 2) * (X m 13 (s * u) * (X m 14 (t * s * u * v ^ 2) * 1))))))))))))) =
      X m 18 (u) * (X m 19 (v) * (X m 20 (u * v) * (X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 6 (s ^ 2 * u) * (X m 7 (t * v) * (X m 9 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 10 (t * s ^ 2 * u * v ^ 2) * (X m 11 (t * s * u * v) * (X m 12 (t * v ^ 2) * (X m 13 (s * u) * (X m 14 (t * s * u * v ^ 2) * 1))))))))))))) := by
  rw [(c_8_7 m (t * s ^ 2 * u * v) (t * v)).left_comm]
  rw [(c_8_6 m (t * s ^ 2 * u * v) (s ^ 2 * u)).left_comm]
  have h2 : X m 7 (t * v) * X m 6 (s ^ 2 * u) =
      X m 6 (s ^ 2 * u) * X m 7 (t * v) * X m 8 (t * s ^ 2 * u * v) * X m 9 (t ^ 2 * s ^ 2 * u * v ^ 2) := by
    have hh := s_7_6 m (t * v) (s ^ 2 * u)
    rw [show (t * v) * (s ^ 2 * u) = t * s ^ 2 * u * v by ring, show (s ^ 2 * u) * (t * v) ^ 2 = t ^ 2 * s ^ 2 * u * v ^ 2 by ring] at hh
    exact hh
  rw [swap_suffix_two h2]
  rw [(c_9_8 m (t ^ 2 * s ^ 2 * u * v ^ 2) (t * s ^ 2 * u * v)).left_comm]
  rw [cancel_suffix (xx m 8 (t * s ^ 2 * u * v))]

private theorem first_seventh_left (m : ℕ) (t s u v : CoefficientField m) :
    X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 18 (u) * (X m 19 (v) * (X m 20 (u * v) * 1))))) =
      X m 18 (u) * (X m 19 (v) * (X m 20 (u * v) * (X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 6 (s ^ 2 * u) * (X m 7 (t * v) * (X m 9 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 10 (t * s ^ 2 * u * v ^ 2) * (X m 11 (t * s * u * v) * (X m 12 (t * v ^ 2) * (X m 13 (s * u) * (X m 14 (t * s * u * v ^ 2) * 1))))))))))))) := by
  calc
    _ = X m 18 (u) * (X m 19 (v) * (X m 20 (u * v) * (X m 0 (t) * (X m 1 (s) * (X m 2 (t * s) * (X m 17 (s * u * v) * (X m 8 (t * s ^ 2 * u * v) * (X m 11 (t * s * u * v) * (X m 6 (s ^ 2 * u) * (X m 7 (t * v) * (X m 8 (t * s ^ 2 * u * v) * (X m 9 (t ^ 2 * s ^ 2 * u * v ^ 2) * (X m 10 (t * s ^ 2 * u * v ^ 2) * (X m 12 (t * v ^ 2) * (X m 13 (s * u) * (X m 17 (s * u * v) * 1)))))))))))))))) := first_seventh_move m t s u v
    _ = _ := by
      simpa only [mul_assoc] using
        congrArg (fun z => (X m 18 (u) * X m 19 (v) * X m 20 (u * v) * X m 0 (t) * X m 1 (s) * X m 2 (t * s)) * z) (first_seventh_corrections m t s u v)

/-- Exact collected split-word exchange for the first-seventh pair. -/
theorem collect_first_seventh (m : ℕ) (t s u v : CoefficientField m) :
    X m 0 (t) * X m 1 (s) * X m 2 (t * s) * X m 18 (u) * X m 19 (v) * X m 20 (u * v) =
      X m 18 (u) * X m 19 (v) * X m 20 (u * v) * X m 0 (t) * X m 1 (s) * X m 2 (t * s) * X m 8 (t * s ^ 2 * u * v) * X m 7 (t * v) * X m 6 (s ^ 2 * u) * X m 10 (t * s ^ 2 * u * v ^ 2) * X m 11 (t * s * u * v) * X m 12 (t * v ^ 2) * X m 13 (s * u) * X m 14 (t * s * u * v ^ 2) := by
  simpa only [mul_one, mul_assoc] using
    (first_seventh_left m t s u v).trans (first_seventh_right m t s u v).symm

end
end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators
