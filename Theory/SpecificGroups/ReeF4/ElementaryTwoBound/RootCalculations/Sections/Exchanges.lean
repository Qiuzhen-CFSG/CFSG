module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Sections.SplitSupport
public import Theory.GroupTheory.FilteredCollection

/-!
# Collection in the six smaller split-root supports

Adjacent root exchanges preserve each displayed support and increase the
positive-root height. Filtered collection therefore gives the ordered supported
factorization in the actual split matrix group. All exchanges are checked
instances of `xc`, `xs`, and `xb`; no finite group enumeration is used.

Source: GLS3 2.4.5(d), 2.4.6 and Lemma 3.3.9.
-/
@[expose] public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.RootCalculations.Sections
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent.OuterElimination
open Theory.AlgebraicGroup.StandardRootSystem
open FilteredCollection
attribute [local irreducible] MatrixRelations.LongCommutators.X

private theorem allowed_d (s : Kind) (i : Fin 24) (hi : Allowed s i) : Allowed .d i := by
  cases s <;> simp_all [Allowed, omitted]

private def negativePairs : List (Fin 24 × Fin 24) :=
  [(2, 17), (2, 20), (2, 21), (3, 16), (3, 20), (3, 21), (4, 12), (4, 21), (5, 13), (5, 20), (6, 7), (6, 12), (6, 16), (7, 6), (7, 13), (7, 17), (12, 4), (12, 6), (12, 13), (13, 5), (13, 7), (13, 12), (16, 3), (16, 6), (17, 2), (17, 7), (20, 2), (20, 3), (20, 5), (21, 2), (21, 3), (21, 4)]

private theorem nonneg_row_2 (j : Fin 24)
    (hj : Allowed .d j) (h : ((2 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 2) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · exact False.elim (h (by decide))
  · exact False.elim (h (by decide))
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_3 (j : Fin 24)
    (hj : Allowed .d j) (h : ((3 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 3) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · exact False.elim (h (by decide))
  · exact False.elim (h (by decide))
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_4 (j : Fin 24)
    (hj : Allowed .d j) (h : ((4 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 4) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_5 (j : Fin 24)
    (hj : Allowed .d j) (h : ((5 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 5) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_6 (j : Fin 24)
    (hj : Allowed .d j) (h : ((6 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 6) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_7 (j : Fin 24)
    (hj : Allowed .d j) (h : ((7 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 7) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_8 (j : Fin 24)
    (hj : Allowed .d j) (h : ((8 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 8) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_9 (j : Fin 24)
    (hj : Allowed .d j) (h : ((9 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 9) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_10 (j : Fin 24)
    (hj : Allowed .d j) (h : ((10 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 10) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_11 (j : Fin 24)
    (hj : Allowed .d j) (h : ((11 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 11) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_12 (j : Fin 24)
    (hj : Allowed .d j) (h : ((12 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 12) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_13 (j : Fin 24)
    (hj : Allowed .d j) (h : ((13 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 13) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_14 (j : Fin 24)
    (hj : Allowed .d j) (h : ((14 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 14) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_15 (j : Fin 24)
    (hj : Allowed .d j) (h : ((15 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 15) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_16 (j : Fin 24)
    (hj : Allowed .d j) (h : ((16 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 16) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_17 (j : Fin 24)
    (hj : Allowed .d j) (h : ((17 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 17) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_20 (j : Fin 24)
    (hj : Allowed .d j) (h : ((20 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 20) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · exact False.elim (h (by decide))
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_row_21 (j : Fin 24)
    (hj : Allowed .d j) (h : ((21 : Fin 24), j) ∉ negativePairs) :
    0 ≤ dot (V 21) (V j) := by
  fin_cases j
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · exact False.elim (h (by decide))
  · exact False.elim (h (by decide))
  · exact False.elim (h (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  · exact False.elim (hj (by decide))
  · exact False.elim (hj (by decide))

private theorem nonneg_of_not_negative (i j : Fin 24)
    (hi : Allowed .d i) (hj : Allowed .d j) (h : (i,j) ∉ negativePairs) :
    0 ≤ dot (V i) (V j) := by
  fin_cases i
  · exact False.elim (hi (by decide))
  · exact False.elim (hi (by decide))
  · exact nonneg_row_2 j hj h
  · exact nonneg_row_3 j hj h
  · exact nonneg_row_4 j hj h
  · exact nonneg_row_5 j hj h
  · exact nonneg_row_6 j hj h
  · exact nonneg_row_7 j hj h
  · exact nonneg_row_8 j hj h
  · exact nonneg_row_9 j hj h
  · exact nonneg_row_10 j hj h
  · exact nonneg_row_11 j hj h
  · exact nonneg_row_12 j hj h
  · exact nonneg_row_13 j hj h
  · exact nonneg_row_14 j hj h
  · exact nonneg_row_15 j hj h
  · exact nonneg_row_16 j hj h
  · exact nonneg_row_17 j hj h
  · exact False.elim (hi (by decide))
  · exact False.elim (hi (by decide))
  · exact nonneg_row_20 j hj h
  · exact nonneg_row_21 j hj h
  · exact False.elim (hi (by decide))
  · exact False.elim (hi (by decide))

def degree : Fin 24 → ℕ :=
  ![1, 1, 2, 3, 5, 4, 4, 3, 7, 10, 9, 6, 5, 3, 8, 11, 7, 5, 2, 2, 4, 6, 1, 1]

private theorem s_2_17 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 2 a * MatrixRelations.LongCommutators.X m 17 b = MatrixRelations.LongCommutators.X m 17 b * MatrixRelations.LongCommutators.X m 2 a * MatrixRelations.LongCommutators.X m 8 (a*b) :=
  xs m 2 17 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_2_20 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 2 a * MatrixRelations.LongCommutators.X m 20 b = MatrixRelations.LongCommutators.X m 20 b * MatrixRelations.LongCommutators.X m 2 a * MatrixRelations.LongCommutators.X m 11 (a*b) :=
  xs m 2 20 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_2_21 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 2 a * MatrixRelations.LongCommutators.X m 21 b = MatrixRelations.LongCommutators.X m 21 b * MatrixRelations.LongCommutators.X m 2 a * MatrixRelations.LongCommutators.X m 14 (a*b) * MatrixRelations.LongCommutators.X m 9 (b*a^2) := by
  simpa only [mul_comm] using xb m 21 2 14 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem s_3_16 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 3 a * MatrixRelations.LongCommutators.X m 16 b = MatrixRelations.LongCommutators.X m 16 b * MatrixRelations.LongCommutators.X m 3 a * MatrixRelations.LongCommutators.X m 9 (a*b) :=
  xs m 3 16 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_3_20 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 3 a * MatrixRelations.LongCommutators.X m 20 b = MatrixRelations.LongCommutators.X m 20 b * MatrixRelations.LongCommutators.X m 3 a * MatrixRelations.LongCommutators.X m 8 (a*b) * MatrixRelations.LongCommutators.X m 15 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 3 20 8 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 8 (a*b)) (xx m 15 (a*b^2))
    (xc m 8 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem s_3_21 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 3 a * MatrixRelations.LongCommutators.X m 21 b = MatrixRelations.LongCommutators.X m 21 b * MatrixRelations.LongCommutators.X m 3 a * MatrixRelations.LongCommutators.X m 10 (a*b) :=
  xs m 3 21 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_4_12 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 4 a * MatrixRelations.LongCommutators.X m 12 b = MatrixRelations.LongCommutators.X m 12 b * MatrixRelations.LongCommutators.X m 4 a * MatrixRelations.LongCommutators.X m 9 (a*b) :=
  xs m 4 12 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_4_21 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 4 a * MatrixRelations.LongCommutators.X m 21 b = MatrixRelations.LongCommutators.X m 21 b * MatrixRelations.LongCommutators.X m 4 a * MatrixRelations.LongCommutators.X m 15 (a*b) :=
  xs m 4 21 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_5_13 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 5 a * MatrixRelations.LongCommutators.X m 13 b = MatrixRelations.LongCommutators.X m 13 b * MatrixRelations.LongCommutators.X m 5 a * MatrixRelations.LongCommutators.X m 8 (a*b) :=
  xs m 5 13 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_5_20 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 5 a * MatrixRelations.LongCommutators.X m 20 b = MatrixRelations.LongCommutators.X m 20 b * MatrixRelations.LongCommutators.X m 5 a * MatrixRelations.LongCommutators.X m 14 (a*b) :=
  xs m 5 20 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_6_7 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 6 a * MatrixRelations.LongCommutators.X m 7 b = MatrixRelations.LongCommutators.X m 7 b * MatrixRelations.LongCommutators.X m 6 a * MatrixRelations.LongCommutators.X m 8 (a*b) * MatrixRelations.LongCommutators.X m 9 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 6 7 8 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 8 (a*b)) (xx m 9 (a*b^2))
    (xc m 8 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem s_6_12 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 6 a * MatrixRelations.LongCommutators.X m 12 b = MatrixRelations.LongCommutators.X m 12 b * MatrixRelations.LongCommutators.X m 6 a * MatrixRelations.LongCommutators.X m 10 (a*b) :=
  xs m 6 12 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_6_16 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 6 a * MatrixRelations.LongCommutators.X m 16 b = MatrixRelations.LongCommutators.X m 16 b * MatrixRelations.LongCommutators.X m 6 a * MatrixRelations.LongCommutators.X m 15 (a*b) :=
  xs m 6 16 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_7_6 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 7 a * MatrixRelations.LongCommutators.X m 6 b = MatrixRelations.LongCommutators.X m 6 b * MatrixRelations.LongCommutators.X m 7 a * MatrixRelations.LongCommutators.X m 8 (a*b) * MatrixRelations.LongCommutators.X m 9 (b*a^2) := by
  simpa only [mul_comm] using xb m 6 7 8 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem s_7_13 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 7 a * MatrixRelations.LongCommutators.X m 13 b = MatrixRelations.LongCommutators.X m 13 b * MatrixRelations.LongCommutators.X m 7 a * MatrixRelations.LongCommutators.X m 11 (a*b) :=
  xs m 7 13 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_7_17 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 7 a * MatrixRelations.LongCommutators.X m 17 b = MatrixRelations.LongCommutators.X m 17 b * MatrixRelations.LongCommutators.X m 7 a * MatrixRelations.LongCommutators.X m 14 (a*b) :=
  xs m 7 17 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_12_4 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 12 a * MatrixRelations.LongCommutators.X m 4 b = MatrixRelations.LongCommutators.X m 4 b * MatrixRelations.LongCommutators.X m 12 a * MatrixRelations.LongCommutators.X m 9 (a*b) :=
  xs m 12 4 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_12_6 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 12 a * MatrixRelations.LongCommutators.X m 6 b = MatrixRelations.LongCommutators.X m 6 b * MatrixRelations.LongCommutators.X m 12 a * MatrixRelations.LongCommutators.X m 10 (a*b) :=
  xs m 12 6 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_12_13 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 12 a * MatrixRelations.LongCommutators.X m 13 b = MatrixRelations.LongCommutators.X m 13 b * MatrixRelations.LongCommutators.X m 12 a * MatrixRelations.LongCommutators.X m 14 (a*b) * MatrixRelations.LongCommutators.X m 15 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 12 13 14 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 14 (a*b)) (xx m 15 (a*b^2))
    (xc m 14 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem s_13_5 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 13 a * MatrixRelations.LongCommutators.X m 5 b = MatrixRelations.LongCommutators.X m 5 b * MatrixRelations.LongCommutators.X m 13 a * MatrixRelations.LongCommutators.X m 8 (a*b) :=
  xs m 13 5 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_13_7 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 13 a * MatrixRelations.LongCommutators.X m 7 b = MatrixRelations.LongCommutators.X m 7 b * MatrixRelations.LongCommutators.X m 13 a * MatrixRelations.LongCommutators.X m 11 (a*b) :=
  xs m 13 7 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_13_12 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 13 a * MatrixRelations.LongCommutators.X m 12 b = MatrixRelations.LongCommutators.X m 12 b * MatrixRelations.LongCommutators.X m 13 a * MatrixRelations.LongCommutators.X m 14 (a*b) * MatrixRelations.LongCommutators.X m 15 (b*a^2) := by
  simpa only [mul_comm] using xb m 12 13 14 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem s_16_3 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 16 a * MatrixRelations.LongCommutators.X m 3 b = MatrixRelations.LongCommutators.X m 3 b * MatrixRelations.LongCommutators.X m 16 a * MatrixRelations.LongCommutators.X m 9 (a*b) :=
  xs m 16 3 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_16_6 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 16 a * MatrixRelations.LongCommutators.X m 6 b = MatrixRelations.LongCommutators.X m 6 b * MatrixRelations.LongCommutators.X m 16 a * MatrixRelations.LongCommutators.X m 15 (a*b) :=
  xs m 16 6 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_17_2 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 17 a * MatrixRelations.LongCommutators.X m 2 b = MatrixRelations.LongCommutators.X m 2 b * MatrixRelations.LongCommutators.X m 17 a * MatrixRelations.LongCommutators.X m 8 (a*b) :=
  xs m 17 2 8 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_17_7 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 17 a * MatrixRelations.LongCommutators.X m 7 b = MatrixRelations.LongCommutators.X m 7 b * MatrixRelations.LongCommutators.X m 17 a * MatrixRelations.LongCommutators.X m 14 (a*b) :=
  xs m 17 7 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_20_2 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 20 a * MatrixRelations.LongCommutators.X m 2 b = MatrixRelations.LongCommutators.X m 2 b * MatrixRelations.LongCommutators.X m 20 a * MatrixRelations.LongCommutators.X m 11 (a*b) :=
  xs m 20 2 11 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_20_3 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 20 a * MatrixRelations.LongCommutators.X m 3 b = MatrixRelations.LongCommutators.X m 3 b * MatrixRelations.LongCommutators.X m 20 a * MatrixRelations.LongCommutators.X m 8 (a*b) * MatrixRelations.LongCommutators.X m 15 (b*a^2) := by
  simpa only [mul_comm] using xb m 3 20 8 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) b a

private theorem s_20_5 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 20 a * MatrixRelations.LongCommutators.X m 5 b = MatrixRelations.LongCommutators.X m 5 b * MatrixRelations.LongCommutators.X m 20 a * MatrixRelations.LongCommutators.X m 14 (a*b) :=
  xs m 20 5 14 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_21_2 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 21 a * MatrixRelations.LongCommutators.X m 2 b = MatrixRelations.LongCommutators.X m 2 b * MatrixRelations.LongCommutators.X m 21 a * MatrixRelations.LongCommutators.X m 14 (a*b) * MatrixRelations.LongCommutators.X m 9 (a*b^2) := by
  simpa only [mul_comm] using reverse_two (xb m 21 2 14 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) (by ext z; fin_cases z <;> norm_num [V]) a b)
    (xx m 14 (a*b)) (xx m 9 (a*b^2))
    (xc m 14 9 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (a*b) (a*b^2))

private theorem s_21_3 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 21 a * MatrixRelations.LongCommutators.X m 3 b = MatrixRelations.LongCommutators.X m 3 b * MatrixRelations.LongCommutators.X m 21 a * MatrixRelations.LongCommutators.X m 10 (a*b) :=
  xs m 21 3 10 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

private theorem s_21_4 (m : ℕ) (a b : CoefficientField m) :
    MatrixRelations.LongCommutators.X m 21 a * MatrixRelations.LongCommutators.X m 4 b = MatrixRelations.LongCommutators.X m 4 b * MatrixRelations.LongCommutators.X m 21 a * MatrixRelations.LongCommutators.X m 15 (a*b) :=
  xs m 21 4 15 (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by norm_num [V, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]) (by ext z; fin_cases z <;> norm_num [V]) a b

theorem exchange (m : ℕ) (s : Kind) (i j : Fin 24)
    (a b : CoefficientField m) (hi : Allowed s i) (hj : Allowed s j) :
    ∃ c : List (Fin 24 × CoefficientField m),
      (∀ z ∈ c, Allowed s z.1 ∧ max (degree i) (degree j) < degree z.1) ∧
      MatrixRelations.LongCommutators.X m i a * MatrixRelations.LongCommutators.X m j b =
        MatrixRelations.LongCommutators.X m j b * MatrixRelations.LongCommutators.X m i a *
          wordProduct (MatrixRelations.LongCommutators.X m) c := by
  by_cases hn : (i,j) ∈ negativePairs
  · simp only [negativePairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hn
    rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl⟩
    · refine ⟨[(8, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_2_17 m a b
    · refine ⟨[(11, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_2_20 m a b
    · refine ⟨[(14, a*b), (9, b*a^2)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_2_21 m a b
    · refine ⟨[(9, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_3_16 m a b
    · refine ⟨[(8, a*b), (15, a*b^2)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_3_20 m a b
    · refine ⟨[(10, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_3_21 m a b
    · refine ⟨[(9, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_4_12 m a b
    · refine ⟨[(15, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_4_21 m a b
    · refine ⟨[(8, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_5_13 m a b
    · refine ⟨[(14, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_5_20 m a b
    · refine ⟨[(8, a*b), (9, a*b^2)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_6_7 m a b
    · refine ⟨[(10, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_6_12 m a b
    · refine ⟨[(15, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_6_16 m a b
    · refine ⟨[(8, a*b), (9, b*a^2)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_7_6 m a b
    · refine ⟨[(11, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_7_13 m a b
    · refine ⟨[(14, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_7_17 m a b
    · refine ⟨[(9, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_12_4 m a b
    · refine ⟨[(10, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_12_6 m a b
    · refine ⟨[(14, a*b), (15, a*b^2)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_12_13 m a b
    · refine ⟨[(8, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_13_5 m a b
    · refine ⟨[(11, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_13_7 m a b
    · refine ⟨[(14, a*b), (15, b*a^2)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_13_12 m a b
    · refine ⟨[(9, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_16_3 m a b
    · refine ⟨[(15, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_16_6 m a b
    · refine ⟨[(8, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_17_2 m a b
    · refine ⟨[(14, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_17_7 m a b
    · refine ⟨[(11, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_20_2 m a b
    · refine ⟨[(8, a*b), (15, b*a^2)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_20_3 m a b
    · refine ⟨[(14, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_20_5 m a b
    · refine ⟨[(14, a*b), (9, a*b^2)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_21_2 m a b
    · refine ⟨[(10, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_21_3 m a b
    · refine ⟨[(15, a*b)], ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl
        all_goals dsimp only [Prod.fst]
        all_goals cases s <;> first
          | exact False.elim (hi (by decide))
          | exact False.elim (hj (by decide))
          | decide
      · simpa only [wordProduct, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, mul_assoc] using s_21_4 m a b
  · refine ⟨[], by simp, ?_⟩
    simpa only [wordProduct, List.map_nil, List.prod_nil, mul_one] using
      (xc m i j (nonneg_of_not_negative i j (allowed_d s i hi) (allowed_d s j hj) hn) a b).eq

end ReeF4.ElementaryTwoBound.RootCalculations.Sections
