module

public import Stellmacher.Recognition.LyonsU3Four.TableIIsolatedLargeGeometry
public import Stellmacher.Recognition.LyonsU3Four.TableIClassificationPairedLarge
public import Stellmacher.Recognition.LyonsU3Four.TableIColumnReflection

/-!
# Finite numerical interface for isolated large differences

After normalizing each row by the sign of its nonzero involution value, the
isolated-orbit saturation condition and local contribution/congruence conditions
provide a finite row-enumeration problem. The explicit search space below has
thirteen constant rows and nineteen four-row Galois orbits. It deliberately
retains locally possible rows that must later be excluded by global Gram
identities. The definitions do not assert coverage or classify multiplicities.

The transfer theorems turn coverage into the exact finite count system, including
the principal row, a large difference, every Gram entry and Galois invariance.
The generic normalization identities are reused from the paired-branch module.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 377–378, Cases 2(b), 3 and 4 and Table I.
-/

@[expose] public section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four
namespace TableIIsolatedRows
open GeneralizedDecompositionData

abbrev rotate := TableIPairedRows.rotate
abbrev z := TableIPairedRows.z
abbrev contribution := TableIPairedRows.contribution
abbrev gram := TableIPairedRows.gram

/-- Candidate rows, ordered with the thirteen constant rows first, then by orbit. -/
def row : Fin 89 → TableIRow := ![
  ![-3, 1, 0, 0, 0, 0],
  ![-3, 1, 1, 1, 1, 1],
  ![-2, 2, 1, 1, 1, 1],
  ![-2, 2, 2, 2, 2, 2],
  ![-1, -1, 1, 1, 1, 1],
  ![-1, 3, 2, 2, 2, 2],
  ![-1, 3, 3, 3, 3, 3],
  ![0, 0, 1, 1, 1, 1],
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 2, 2, 2, 2],
  ![2, 2, 1, 1, 1, 1],
  ![2, 2, 2, 2, 2, 2],
  ![-2, 0, 0, 0, 1, 1],
  ![-2, 0, 1, 0, 0, 1],
  ![-2, 0, 1, 1, 0, 0],
  ![-2, 0, 0, 1, 1, 0],
  ![-1, 1, 0, 0, 1, 1],
  ![-1, 1, 1, 0, 0, 1],
  ![-1, 1, 1, 1, 0, 0],
  ![-1, 1, 0, 1, 1, 0],
  ![-1, 1, 1, 1, 2, 2],
  ![-1, 1, 2, 1, 1, 2],
  ![-1, 1, 2, 2, 1, 1],
  ![-1, 1, 1, 2, 2, 1],
  ![0, 0, 0, 1, 1, 2],
  ![0, 0, 2, 0, 1, 1],
  ![0, 0, 1, 2, 0, 1],
  ![0, 0, 1, 1, 2, 0],
  ![0, 0, 0, 1, 2, 1],
  ![0, 0, 1, 0, 1, 2],
  ![0, 0, 2, 1, 0, 1],
  ![0, 0, 1, 2, 1, 0],
  ![0, 0, 0, 2, 1, 1],
  ![0, 0, 1, 0, 2, 1],
  ![0, 0, 1, 1, 0, 2],
  ![0, 0, 2, 1, 1, 0],
  ![0, 2, 0, 0, 1, 1],
  ![0, 2, 1, 0, 0, 1],
  ![0, 2, 1, 1, 0, 0],
  ![0, 2, 0, 1, 1, 0],
  ![0, 2, 1, 1, 2, 2],
  ![0, 2, 2, 1, 1, 2],
  ![0, 2, 2, 2, 1, 1],
  ![0, 2, 1, 2, 2, 1],
  ![0, 2, 2, 2, 3, 3],
  ![0, 2, 3, 2, 2, 3],
  ![0, 2, 3, 3, 2, 2],
  ![0, 2, 2, 3, 3, 2],
  ![1, -1, 0, 0, 1, 1],
  ![1, -1, 1, 0, 0, 1],
  ![1, -1, 1, 1, 0, 0],
  ![1, -1, 0, 1, 1, 0],
  ![1, 1, -1, 0, 0, 1],
  ![1, 1, 1, -1, 0, 0],
  ![1, 1, 0, 1, -1, 0],
  ![1, 1, 0, 0, 1, -1],
  ![1, 1, -1, 0, 1, 0],
  ![1, 1, 0, -1, 0, 1],
  ![1, 1, 1, 0, -1, 0],
  ![1, 1, 0, 1, 0, -1],
  ![1, 1, -1, 1, 0, 0],
  ![1, 1, 0, -1, 1, 0],
  ![1, 1, 0, 0, -1, 1],
  ![1, 1, 1, 0, 0, -1],
  ![1, 1, 0, 1, 1, 2],
  ![1, 1, 2, 0, 1, 1],
  ![1, 1, 1, 2, 0, 1],
  ![1, 1, 1, 1, 2, 0],
  ![1, 1, 0, 1, 2, 1],
  ![1, 1, 1, 0, 1, 2],
  ![1, 1, 2, 1, 0, 1],
  ![1, 1, 1, 2, 1, 0],
  ![1, 1, 0, 2, 1, 1],
  ![1, 1, 1, 0, 2, 1],
  ![1, 1, 1, 1, 0, 2],
  ![1, 1, 2, 1, 1, 0],
  ![1, 3, 2, 2, 3, 3],
  ![1, 3, 3, 2, 2, 3],
  ![1, 3, 3, 3, 2, 2],
  ![1, 3, 2, 3, 3, 2],
  ![2, 0, 0, 0, 1, 1],
  ![2, 0, 1, 0, 0, 1],
  ![2, 0, 1, 1, 0, 0],
  ![2, 0, 0, 1, 1, 0],
  ![3, 1, 0, 0, 1, 1],
  ![3, 1, 1, 0, 0, 1],
  ![3, 1, 1, 1, 0, 0],
  ![3, 1, 0, 1, 1, 0]]

def rotation : Fin 89 → Fin 89 := ![
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 13, 18, 19, 20, 17, 22, 23, 24, 21, 26, 27, 28, 25, 30, 31, 32, 29, 34, 35, 36, 33, 38, 39, 40, 37, 42, 43, 44, 41, 46, 47, 48, 45, 50, 51, 52, 49, 54, 55, 56, 53, 58, 59, 60, 57, 62, 63, 64, 61, 66, 67, 68, 65, 70, 71, 72, 69, 74, 75, 76, 73, 78, 79, 80, 77, 82, 83, 84, 81, 86, 87, 88, 85]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem row_injective : Function.Injective row := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem row_rotation (k : Fin 89) : row (rotation k) = rotate (row k) := by
  revert k; decide +kernel

/-- Column reflection on six-entry rows, fixing the first two entries. -/
def reflect (r : TableIRow) : TableIRow := ![r 0, r 1, r 3, r 2, r 5, r 4]

@[simp] theorem reflect_twice (r : TableIRow) : reflect (reflect r) = r := by
  funext k; fin_cases k <;> rfl

def reflection : Fin 89 → Fin 89 := ![
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 15, 14, 17, 20, 19, 18, 21, 24, 23, 22, 34, 33, 36, 35, 30, 29, 32, 31, 26, 25, 28, 27, 37, 40, 39, 38, 41, 44, 43, 42, 45, 48, 47, 46, 49, 52, 51, 50, 62, 61, 64, 63, 58, 57, 60, 59, 54, 53, 56, 55, 74, 73, 76, 75, 70, 69, 72, 71, 66, 65, 68, 67, 77, 80, 79, 78, 81, 84, 83, 82, 85, 88, 87, 86]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem row_reflection (k : Fin 89) : row (reflection k) = reflect (row k) := by
  revert k; decide +kernel

def principal : Fin 89 := 8

theorem row_principal : row principal = ![1,1,0,0,0,0] := rfl

def difference (r : TableIRow) (i : Fin 4) : ℤ :=
  r (![2,3,4,5] i) - r (![3,4,5,2] i)

/-- Local constraints after applying the global isolated-orbit saturation theorem. -/
structure Admissible (r : TableIRow) : Prop where
  contribution_lt : contribution r < 64
  congruence : Int.ModEq 4 (r 0) (z r)
  z_pos : 0 < z r
  support : IsolatedDifferenceSupport (difference r)

/-- Complete numerical input for classifying the multiplicities. -/
structure MultiplicityConditions (n : Fin 89 → ℕ) : Prop where
  principal_pos : 0 < n principal
  large_pos : ∃ a, 0 < n a ∧ difference (row a) 0 ^ 2 = 4
  rotation_eq : ∀ a, n (rotation a) = n a
  gram_eq : ∀ k l, ∑ a, (n a : ℤ) * row a k * row a l = gram k l

end TableIIsolatedRows
end Stellmacher.Recognition.LyonsU3Four

namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
variable {I : Type*} (d : GeneralizedDecompositionData I)

private theorem isolated_sign_product (j : I) (x y : ℤ) :
    (d.tableIRowSign j*x)*(d.tableIRowSign j*y) = x*y := by
  calc
    _ = d.tableIRowSign j^2*(x*y) := by ring
    _ = x*y := by rw [d.tableIRowSign_sq, one_mul]

private theorem isolated_sign_square (j : I) (x : ℤ) :
    (d.tableIRowSign j*x)^2 = x^2 := by
  simpa only [pow_two] using d.isolated_sign_product j x x

private theorem isolated_normalized_z (j : I) :
    TableIIsolatedRows.z (d.normalizedTableIRow j) = d.tableIRowSign j*d.zValue j := by
  simp only [TableIIsolatedRows.z, TableIPairedRows.z, normalizedTableIRow,
    tableIRow_succ, zValue, Finset.mul_sum]

/-- Normalized adjacent differences are multiplied by the same row sign. -/
theorem isolated_normalized_difference (j : I) (i : Fin 4) :
    TableIIsolatedRows.difference (d.normalizedTableIRow j) i =
      d.tableIRowSign j * d.adjacentDifference i j := by
  fin_cases i <;>
    simp [TableIIsolatedRows.difference, normalizedTableIRow, tableIRow, adjacentDifference] <;>
    ring

/-- Normalization commutes with column reflection. -/
theorem isolated_normalized_reflection (j : I) :
    d.reflectColumns.normalizedTableIRow j =
      TableIIsolatedRows.reflect (d.normalizedTableIRow j) := by
  have hs : d.reflectColumns.tableIRowSign j = d.tableIRowSign j := by
    simp only [tableIRowSign, reflectColumns_zValue]
  funext k
  fin_cases k <;> simp only [normalizedTableIRow, hs] <;> rfl

variable [Fintype I]

/-- Every normalized row satisfies the local isolated-support constraints. -/
theorem isolated_normalized_admissible {principal : I}
    (h : d.TableIPatternHypotheses principal) (hi : d.HasIsolatedLargeDifference)
    (j : I) : TableIIsolatedRows.Admissible (d.normalizedTableIRow j) := by
  constructor
  · have hd (x y : ℤ) :
        (d.tableIRowSign j*x - d.tableIRowSign j*y)^2 = (x-y)^2 := by
      rw [← mul_sub, d.isolated_sign_square]
    simpa only [TableIIsolatedRows.contribution, TableIPairedRows.contribution,
      normalizedTableIRow, tableIRow_zero, tableIRow_succ, d.isolated_sign_square,
      hd, contribution] using h.equation_3_3 j
  · rw [d.isolated_normalized_z]
    exact (h.equation_3_4 j).mul_left (d.tableIRowSign j)
  · rw [d.isolated_normalized_z]
    have hn := h.z_nonzero j
    unfold tableIRowSign
    split <;> simp only [one_mul, neg_one_mul] <;> omega
  · have hh := (d.isolated_difference_support h.equation_3_2 h.galois_symmetry hi j).mul
      (d.tableIRowSign j) (d.tableIRowSign_sq j)
    convert hh using 1
    funext i
    exact d.isolated_normalized_difference j i

/-- Sum a row statistic using its full multiplicities in the isolated support. -/
theorem isolated_sum_by_multiplicity
    (hcover : ∀ j, ∃ a, d.normalizedTableIRow j = TableIIsolatedRows.row a)
    (f : TableIRow → ℤ) :
    ∑ a, (d.tableIRowMultiplicity (TableIIsolatedRows.row a) : ℤ) *
      f (TableIIsolatedRows.row a) = ∑ j, f (d.normalizedTableIRow j) := by
  classical
  have hn (a : Fin 89) : (d.tableIRowMultiplicity (TableIIsolatedRows.row a) : ℤ) =
      ∑ j, if d.normalizedTableIRow j = TableIIsolatedRows.row a then 1 else 0 := by
    rw [tableIRowMultiplicity, Fintype.card_subtype, Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [hn, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨a, ha⟩ := hcover j
  have he (b : Fin 89) : d.normalizedTableIRow j = TableIIsolatedRows.row b ↔ b = a := by
    rw [ha]
    exact TableIIsolatedRows.row_injective.eq_iff.trans eq_comm
  simp only [he]
  simp [ha]

/-- Once coverage is established, all remaining hypotheses are finite linear
constraints on the multiplicities of the explicit candidate rows. -/
theorem isolated_multiplicity_conditions {principal : I}
    (h : d.TableIPatternHypotheses principal) (hi : d.HasIsolatedLargeDifference)
    (hcover : ∀ j, ∃ a, d.normalizedTableIRow j = TableIIsolatedRows.row a) :
    TableIIsolatedRows.MultiplicityConditions
      (fun a => d.tableIRowMultiplicity (TableIIsolatedRows.row a)) := by
  classical
  constructor
  · apply Fintype.card_pos_iff.mpr
    exact ⟨⟨principal, (d.normalizedTableIRow_principal principal h).trans
      TableIIsolatedRows.row_principal.symm⟩⟩
  · obtain ⟨j, ε, hε, hj⟩ := hi
    obtain ⟨a, ha⟩ := hcover j
    refine ⟨a, Fintype.card_pos_iff.mpr ⟨⟨j, ha⟩⟩, ?_⟩
    rw [← ha, d.isolated_normalized_difference, d.isolated_sign_square]
    have he := congrFun hj 0
    change d.adjacentDifference 0 j = ε*2 at he
    rw [he, mul_pow, hε]
    norm_num
  · intro a
    rw [TableIIsolatedRows.row_rotation]
    exact d.paired_multiplicity_rotate h _
  · intro k l
    simpa only [mul_assoc] using
      (d.isolated_sum_by_multiplicity hcover (fun r => r k*r l)).trans
        (d.paired_normalized_gram h k l)

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
