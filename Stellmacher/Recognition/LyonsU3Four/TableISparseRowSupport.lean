module

public import Stellmacher.Recognition.LyonsU3Four.TableIDifferenceColumns
public import Stellmacher.Recognition.LyonsU3Four.TableIRowMultiplicity
public import Mathlib.Tactic.IntervalCases

/-!
# Support for the sparse branch of Lyons's Table I enumeration

When large, consecutive, and opposite unit differences are absent, the two
opposite products of adjacent differences vanish in every row. The proof first
shows that each product is nonnegative, then uses its zero column inner product.

The explicit list below is a finite search space for normalized rows. It is not
an exhaustiveness assertion: local coverage and classification of its possible
multiplicities are separate theorems. All repetitions in an ambient matrix are
retained by `tableIRowMultiplicity`.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 379–380, Table II and Case 6.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open scoped BigOperators

namespace TableISparseRows

/-- Rotate the four nonprincipal involution entries in the Galois direction. -/
def rotate (r : TableIRow) : TableIRow :=
  ![r 0, r 1, r 5, r 2, r 3, r 4]

theorem rotate_injective : Function.Injective rotate := by
  intro r s h
  funext k
  fin_cases k
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 3
  · exact congrFun h 4
  · exact congrFun h 5
  · exact congrFun h 2

/-- Positive-at-z row candidates, including constant and single-exception rows. -/
def row : Fin 85 → TableIRow := ![
  ![-3, 0, 0, 0, 0, 1],
  ![-3, 0, 0, 0, 1, 0],
  ![-3, 0, 0, 1, 0, 0],
  ![-3, 0, 1, 0, 0, 0],
  ![-3, 1, 0, 0, 0, 0],
  ![-3, 1, 1, 1, 1, 1],
  ![-2, 1, 0, 0, 0, 1],
  ![-2, 1, 0, 0, 1, 0],
  ![-2, 1, 0, 1, 0, 0],
  ![-2, 1, 1, 0, 0, 0],
  ![-2, 1, 1, 1, 1, 2],
  ![-2, 1, 1, 1, 2, 1],
  ![-2, 1, 1, 2, 1, 1],
  ![-2, 1, 2, 1, 1, 1],
  ![-2, 2, 1, 1, 1, 1],
  ![-2, 2, 2, 2, 2, 2],
  ![-1, -1, 1, 1, 1, 1],
  ![-1, 0, 0, 1, 1, 1],
  ![-1, 0, 1, 0, 1, 1],
  ![-1, 0, 1, 1, 0, 1],
  ![-1, 0, 1, 1, 1, 0],
  ![-1, 2, 0, 0, 0, 1],
  ![-1, 2, 0, 0, 1, 0],
  ![-1, 2, 0, 1, 0, 0],
  ![-1, 2, 1, 0, 0, 0],
  ![-1, 2, 1, 1, 1, 2],
  ![-1, 2, 1, 1, 2, 1],
  ![-1, 2, 1, 2, 1, 1],
  ![-1, 2, 2, 1, 1, 1],
  ![-1, 2, 2, 2, 2, 3],
  ![-1, 2, 2, 2, 3, 2],
  ![-1, 2, 2, 3, 2, 2],
  ![-1, 2, 3, 2, 2, 2],
  ![-1, 3, 2, 2, 2, 2],
  ![-1, 3, 3, 3, 3, 3],
  ![0, 0, 1, 1, 1, 1],
  ![0, 1, 0, 1, 1, 1],
  ![0, 1, 1, 0, 1, 1],
  ![0, 1, 1, 1, 0, 1],
  ![0, 1, 1, 1, 1, 0],
  ![0, 1, 1, 2, 2, 2],
  ![0, 1, 2, 1, 2, 2],
  ![0, 1, 2, 2, 1, 2],
  ![0, 1, 2, 2, 2, 1],
  ![0, 3, 2, 2, 2, 3],
  ![0, 3, 2, 2, 3, 2],
  ![0, 3, 2, 3, 2, 2],
  ![0, 3, 3, 2, 2, 2],
  ![1, 0, 0, 0, 0, 1],
  ![1, 0, 0, 0, 1, 0],
  ![1, 0, 0, 1, 0, 0],
  ![1, 0, 1, 0, 0, 0],
  ![1, 0, 1, 1, 1, 2],
  ![1, 0, 1, 1, 2, 1],
  ![1, 0, 1, 2, 1, 1],
  ![1, 0, 2, 1, 1, 1],
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 2, 2, 2, 2],
  ![1, 2, 0, 1, 1, 1],
  ![1, 2, 1, 0, 1, 1],
  ![1, 2, 1, 1, 0, 1],
  ![1, 2, 1, 1, 1, 0],
  ![1, 2, 1, 2, 2, 2],
  ![1, 2, 2, 1, 2, 2],
  ![1, 2, 2, 2, 1, 2],
  ![1, 2, 2, 2, 2, 1],
  ![1, 2, 2, 3, 3, 3],
  ![1, 2, 3, 2, 3, 3],
  ![1, 2, 3, 3, 2, 3],
  ![1, 2, 3, 3, 3, 2],
  ![2, 1, 0, 0, 0, 1],
  ![2, 1, 0, 0, 1, 0],
  ![2, 1, 0, 1, 0, 0],
  ![2, 1, 1, 0, 0, 0],
  ![2, 1, 1, 1, 1, 2],
  ![2, 1, 1, 1, 2, 1],
  ![2, 1, 1, 2, 1, 1],
  ![2, 1, 2, 1, 1, 1],
  ![2, 2, 1, 1, 1, 1],
  ![2, 2, 2, 2, 2, 2],
  ![3, 0, 0, 1, 1, 1],
  ![3, 0, 1, 0, 1, 1],
  ![3, 0, 1, 1, 0, 1],
  ![3, 0, 1, 1, 1, 0]]

/-- The permutation of the candidate indices induced by Galois rotation. -/
def rotation : Fin 85 → Fin 85 := ![
  3, 0, 1, 2, 4, 5, 9, 6, 7, 8, 13, 10, 11, 12, 14, 15, 16, 18, 19, 20, 17, 24, 21, 22, 23, 28, 25, 26, 27, 32, 29, 30, 31, 33, 34, 35, 37, 38, 39, 36, 41, 42, 43, 40, 47, 44, 45, 46, 51, 48, 49, 50, 55, 52, 53, 54, 56, 57, 58, 60, 61, 62, 59, 64, 65, 66, 63, 68, 69, 70, 67, 74, 71, 72, 73, 78, 75, 76, 77, 79, 80, 82, 83, 84, 81]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem row_injective : Function.Injective row := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem row_rotation (k : Fin 85) : row (rotation k) = rotate (row k) := by
  revert k
  decide

/-- The principal row's index in this finite search space. -/
def principal : Fin 85 := 56

theorem row_principal : row principal = ![1, 1, 0, 0, 0, 0] := by decide

/-- Sum of the five involution entries. -/
def z (r : TableIRow) : ℤ := ∑ i : Fin 5, r i.succ

/-- Contribution numerator for one six-entry row. -/
def contribution (r : TableIRow) : ℤ :=
  4 * r 0 ^ 2 + (∑ i : Fin 5, r i.succ ^ 2) +
    3 * ∑ i : Fin 5, ∑ k ∈ Finset.Iio i, (r k.succ - r i.succ) ^ 2

/-- The four adjacent differences of a six-entry row. -/
def difference (r : TableIRow) (i : Fin 4) : ℤ :=
  r (![2, 3, 4, 5] i) - r (![3, 4, 5, 2] i)

/-- The local numerical constraints to be used for finite row coverage. -/
structure Admissible (r : TableIRow) : Prop where
  contribution_lt : contribution r < 64
  congruence : Int.ModEq 4 (r 0) (z r)
  z_pos : 0 < z r
  unit_bounds : ∀ i, -1 ≤ difference r i ∧ difference r i ≤ 1
  opposite_zero : difference r 0 * difference r 2 = 0 ∧
    difference r 1 * difference r 3 = 0

/-- The six-column Gram matrix prescribed by equation (3.2). -/
def gram (k l : Fin 6) : ℤ :=
  if k = 0 then (if l = 0 then 16 else 0)
  else if l = 0 then 0 else 4 * (3 + if k = l then 1 else 0)

/-- Numerical conditions on the full multiplicity vector. -/
structure MultiplicityConditions (n : Fin 85 → ℕ) : Prop where
  principal_pos : 0 < n principal
  galois : ∀ k, n (rotation k) = n k
  gram_eq : ∀ k l, ∑ a, (n a : ℤ) * row a k * row a l = gram k l

end TableISparseRows

namespace GeneralizedDecompositionData
private theorem opposite_nonneg (a b c e : ℤ)
    (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1)
    (hc : -1 ≤ c ∧ c ≤ 1) (he : -1 ≤ e ∧ e ≤ 1)
    (hs : a + b + c + e = 0) (hab : a * b ≠ 1) (hbc : b * c ≠ 1)
    (ho : ¬ ((a = 1 ∧ b = 0 ∧ c = -1 ∧ e = 0) ∨
      (a = -1 ∧ b = 0 ∧ c = 1 ∧ e = 0))) : 0 ≤ a * c := by
  rcases ha with ⟨ha₀, ha₁⟩
  rcases hb with ⟨hb₀, hb₁⟩
  rcases hc with ⟨hc₀, hc₁⟩
  rcases he with ⟨he₀, he₁⟩
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases e <;>
    norm_num at *

variable {I : Type*} [Fintype I] (d : GeneralizedDecompositionData I)
/-- Opposite difference entries cannot both be nonzero in this branch. -/
theorem sparse_first_opposite_product {principal : I} (h : d.TableIPatternHypotheses principal)
    (hl : ¬ d.HasLargeDifference) (hc : ¬ d.HasConsecutiveUnitDifferences)
    (ho : ¬ d.HasOppositeUnitDifferences) (j : I) :
    d.adjacentDifference 0 j * d.adjacentDifference 2 j = 0 := by
  obtain ⟨σ, hσ⟩ := h.galois_symmetry.adjacentDifference d
  have hn (k : I) : 0 ≤ d.adjacentDifference 0 k * d.adjacentDifference 2 k := by
    apply opposite_nonneg
      (d.adjacentDifference 0 k) (d.adjacentDifference 1 k)
      (d.adjacentDifference 2 k) (d.adjacentDifference 3 k)
      (h.equation_3_2.unit_bounds_of_not_large d hl 0 k)
      (h.equation_3_2.unit_bounds_of_not_large d hl 1 k)
      (h.equation_3_2.unit_bounds_of_not_large d hl 2 k)
      (h.equation_3_2.unit_bounds_of_not_large d hl 3 k)
    · simpa [Fin.sum_univ_succ, add_assoc] using d.adjacentDifference_sum k
    · exact fun he => hc ⟨k, he⟩
    · intro he
      apply hc
      refine ⟨σ k, ?_⟩
      rw [hσ k 1, hσ k 2] at he
      exact he
    · rintro (he | he) <;> apply ho <;> refine ⟨k, ?_⟩
      · left; rcases he with ⟨ha, hb, hc, he⟩
        funext i; fin_cases i <;> simp [ha, hb, hc, he]
      · right; rcases he with ⟨ha, hb, hc, he⟩
        funext i; fin_cases i <;> simp [ha, hb, hc, he]
  have hs := h.equation_3_2.adjacentDifference_inner d 0 2
  exact ((Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hn k)).mp hs) j (Finset.mem_univ j)

theorem sparse_opposite_products {principal : I}
    (h : d.TableIPatternHypotheses principal)
    (hl : ¬ d.HasLargeDifference) (hc : ¬ d.HasConsecutiveUnitDifferences)
    (ho : ¬ d.HasOppositeUnitDifferences) (j : I) :
    d.adjacentDifference 0 j * d.adjacentDifference 2 j = 0 ∧
    d.adjacentDifference 1 j * d.adjacentDifference 3 j = 0 := by
  refine ⟨d.sparse_first_opposite_product h hl hc ho j, ?_⟩
  obtain ⟨σ, hσ⟩ := h.galois_symmetry.adjacentDifference d
  rw [hσ j 1, hσ j 3]
  exact d.sparse_first_opposite_product h hl hc ho (σ j)

end GeneralizedDecompositionData
end Stellmacher.Recognition.LyonsU3Four
