module

public import Stellmacher.Recognition.LyonsU3Four.TableISparseOppositeRows

/-!
# Exhaustive support for sparse Table I rows

The contribution inequality bounds the first three normalized entries by three:
for each involution entry, completing squares writes the contribution minus
four times its square as a sum of squares. The next three entries are encoded
by their unit differences. A kernel-checked enumeration of these 9,261 bounded
choices proves coverage by the 51 rotation orbits, without assuming catalogue
exhaustiveness.

For an arbitrary decomposition matrix, Galois symmetry transports the absence
of consecutive equal unit differences to all four adjacent pairs. Normalizing
the sign of each row preserves contribution, congruence, and difference products,
and makes the involution value positive. Thus the finite coverage theorem
applies to every normalized row, with multiplicities left to the consumer.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 379–380, Table II and Cases 6–8.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four.SparseOppositeRows
private theorem contribution_bounds (r : TableIRow) (h : contribution r < 64) :
    (-3 ≤ r 0 ∧ r 0 ≤ 3) ∧ (-3 ≤ r 1 ∧ r 1 ≤ 3) ∧ (-3 ≤ r 2 ∧ r 2 ≤ 3) := by
  unfold contribution at h
  have ht : 4 * r 0 ^ 2 < 64 := by
    nlinarith only [h, sq_nonneg (r 1), sq_nonneg (r 2), sq_nonneg (r 3),
      sq_nonneg (r 4), sq_nonneg (r 5), sq_nonneg (r 1-r 2), sq_nonneg (r 1-r 3),
      sq_nonneg (r 1-r 4), sq_nonneg (r 1-r 5), sq_nonneg (r 2-r 3),
      sq_nonneg (r 2-r 4), sq_nonneg (r 2-r 5), sq_nonneg (r 3-r 4),
      sq_nonneg (r 3-r 5), sq_nonneg (r 4-r 5)]
  have ha : 4 * r 1 ^ 2 < 64 := by
    nlinarith only [h, sq_nonneg (r 0), sq_nonneg (3*r 1-r 2-r 3-r 4-r 5),
      sq_nonneg (r 2-r 3), sq_nonneg (r 2-r 4), sq_nonneg (r 2-r 5),
      sq_nonneg (r 3-r 4), sq_nonneg (r 3-r 5), sq_nonneg (r 4-r 5)]
  have hb : 4 * r 2 ^ 2 < 64 := by
    nlinarith only [h, sq_nonneg (r 0), sq_nonneg (3*r 2-r 1-r 3-r 4-r 5),
      sq_nonneg (r 1-r 3), sq_nonneg (r 1-r 4), sq_nonneg (r 1-r 5),
      sq_nonneg (r 3-r 4), sq_nonneg (r 3-r 5), sq_nonneg (r 4-r 5)]
  exact ⟨⟨by nlinarith only [ht], by nlinarith only [ht]⟩,
    ⟨by nlinarith only [ha], by nlinarith only [ha]⟩,
    ⟨by nlinarith only [hb], by nlinarith only [hb]⟩⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem finite_coverage (t : Fin 7) (a b : Fin 7) (q w e : Fin 3) :
    let r : TableIRow := ![(t : ℤ) - 3, (a : ℤ) - 3, (b : ℤ) - 3,
      (b : ℤ) - 3 - ((q : ℤ) - 1),
      (b : ℤ) - 3 - ((q : ℤ) - 1) - ((w : ℤ) - 1),
      (b : ℤ) - 3 - ((q : ℤ) - 1) - ((w : ℤ) - 1) - ((e : ℤ) - 1)]
    Admissible r → ∃ p k, r = rotation (representative p) k := by
  revert t a b q w e
  decide +kernel

private theorem bounded_fin (x : ℤ) (n : ℕ) (h : -(n : ℤ) ≤ x ∧ x ≤ n) :
    ∃ k : Fin (2*n+1), x = (k : ℤ) - n := by
  refine ⟨⟨(x+n).toNat, by omega⟩, ?_⟩
  change x = ((x+n).toNat : ℤ) - n
  omega

/-- Every locally admissible integral row belongs to a listed rotation orbit. -/
theorem admissible_covered (r : TableIRow) (h : Admissible r) :
    ∃ p, r ∈ orbit p := by
  obtain ⟨ht, ha, hb⟩ := contribution_bounds r h.2.1
  obtain ⟨t, ht⟩ := bounded_fin (r 0) 3 ht
  obtain ⟨a, ha⟩ := bounded_fin (r 1) 3 ha
  obtain ⟨b, hb⟩ := bounded_fin (r 2) 3 hb
  have hq := h.2.2.2.1 0
  have hw := h.2.2.2.1 1
  have he := h.2.2.2.1 2
  change -1 ≤ r 2-r 3 ∧ r 2-r 3 ≤ 1 at hq
  change -1 ≤ r 3-r 4 ∧ r 3-r 4 ≤ 1 at hw
  change -1 ≤ r 4-r 5 ∧ r 4-r 5 ≤ 1 at he
  obtain ⟨q, hq⟩ := bounded_fin (r 2-r 3) 1 hq
  obtain ⟨w, hw⟩ := bounded_fin (r 3-r 4) 1 hw
  obtain ⟨e, he⟩ := bounded_fin (r 4-r 5) 1 he
  have hr : r = ![(t : ℤ) - 3, (a : ℤ) - 3, (b : ℤ) - 3,
      (b : ℤ) - 3 - ((q : ℤ) - 1),
      (b : ℤ) - 3 - ((q : ℤ) - 1) - ((w : ℤ) - 1),
      (b : ℤ) - 3 - ((q : ℤ) - 1) - ((w : ℤ) - 1) - ((e : ℤ) - 1)] := by
    funext i
    fin_cases i <;> simp <;> omega
  rw [hr] at h ⊢
  obtain ⟨p, k, hk⟩ := finite_coverage t a b q w e h
  refine ⟨p, ?_⟩
  rw [hk]
  exact rotation_mem_orbit p k

end Stellmacher.Recognition.LyonsU3Four.SparseOppositeRows

open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four
namespace GeneralizedDecompositionData
variable {I : Type*} (d : GeneralizedDecompositionData I)
private theorem sign_product (j : I) (x y : ℤ) :
    (d.tableIRowSign j * x) * (d.tableIRowSign j * y) = x * y := by
  calc
    _ = d.tableIRowSign j ^ 2 * (x * y) := by ring
    _ = x * y := by rw [d.tableIRowSign_sq, one_mul]
private theorem sign_square (j : I) (x : ℤ) :
    (d.tableIRowSign j * x) ^ 2 = x ^ 2 := by
  simpa only [pow_two] using d.sign_product j x x
private theorem normalized_value (j : I) :
    SparseOppositeRows.value (d.normalizedTableIRow j) =
      d.tableIRowSign j * d.zValue j := by
  simp [SparseOppositeRows.value, normalizedTableIRow, tableIRow, zValue,
    Fin.sum_univ_succ]
  ring
private theorem normalized_difference (j : I) (i : Fin 4) :
    SparseOppositeRows.difference (d.normalizedTableIRow j) i =
      d.tableIRowSign j * d.adjacentDifference i j := by
  fin_cases i <;> simp [SparseOppositeRows.difference, normalizedTableIRow,
    adjacentDifference, tableIRow] <;> ring
private theorem normalized_contribution (j : I) :
    SparseOppositeRows.contribution (d.normalizedTableIRow j) = d.contribution j := by
  have hi (i : Fin 5) : Finset.Iio i = Finset.univ.filter (· < i) := by
    ext k; simp
  have hd (x y : ℤ) :
      (d.tableIRowSign j * x - d.tableIRowSign j * y) ^ 2 = (x - y) ^ 2 := by
    rw [← mul_sub, d.sign_square]
  simp [SparseOppositeRows.contribution, normalizedTableIRow, tableIRow,
    sign_square, hd, contribution, hi, Finset.sum_filter, Fin.sum_univ_succ]
  ring
variable [Fintype I]
/-- Galois symmetry excludes consecutive equal unit differences at every pair. -/
theorem sparse_adjacent_products_ne_one {principal : I}
    (h : d.TableIPatternHypotheses principal)
    (hc : ¬ d.HasConsecutiveUnitDifferences) (j : I) (i : Fin 4) :
    d.adjacentDifference i j * d.adjacentDifference (![1, 2, 3, 0] i) j ≠ 1 := by
  obtain ⟨σ, hσ⟩ := h.galois_symmetry.adjacentDifference d
  have h0 (k : I) : d.adjacentDifference 0 k * d.adjacentDifference 1 k ≠ 1 :=
    fun he => hc ⟨k, he⟩
  have h1 (k : I) : d.adjacentDifference 1 k * d.adjacentDifference 2 k ≠ 1 := by
    rw [hσ k 1, hσ k 2]
    exact h0 (σ k)
  have h2 (k : I) : d.adjacentDifference 2 k * d.adjacentDifference 3 k ≠ 1 := by
    rw [hσ k 2, hσ k 3]
    exact h1 (σ k)
  have h3 (k : I) : d.adjacentDifference 3 k * d.adjacentDifference 0 k ≠ 1 := by
    rw [hσ k 3, hσ k 0]
    exact h2 (σ k)
  fin_cases i
  · exact h0 j
  · exact h1 j
  · exact h2 j
  · exact h3 j

/-- Orienting a sparse row by its involution value gives the local catalogue conditions. -/
theorem normalized_sparse_opposite_admissible {principal : I}
    (h : d.TableIPatternHypotheses principal)
    (hl : ¬ d.HasLargeDifference) (hc : ¬ d.HasConsecutiveUnitDifferences) (j : I) :
    SparseOppositeRows.Admissible (d.normalizedTableIRow j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [d.normalized_value]
    have hn := h.z_nonzero j
    unfold tableIRowSign
    split <;> simp only [one_mul, neg_one_mul] <;> omega
  · rw [d.normalized_contribution]
    exact h.equation_3_3 j
  · rw [d.normalized_value]
    exact (h.equation_3_4 j).mul_left (d.tableIRowSign j)
  · intro i
    rw [d.normalized_difference]
    have hb := h.equation_3_2.unit_bounds_of_not_large d hl i j
    rcases sq_eq_one_iff.mp (d.tableIRowSign_sq j) with hs | hs
    · simpa only [hs, one_mul] using hb
    · rw [hs, neg_one_mul]
      omega
  · intro i
    simp only [d.normalized_difference, d.sign_product]
    exact d.sparse_adjacent_products_ne_one h hc j i

/-- Every normalized row in the sparse branch lies in one of the 51 listed
rotation orbits. No assumption about an opposite pair is needed for support. -/
theorem normalized_sparse_opposite_supported {principal : I}
    (h : d.TableIPatternHypotheses principal)
    (hl : ¬ d.HasLargeDifference) (hc : ¬ d.HasConsecutiveUnitDifferences) :
    ∀ j, ∃ p, d.normalizedTableIRow j ∈ SparseOppositeRows.orbit p := by
  intro j
  exact SparseOppositeRows.admissible_covered _
    (d.normalized_sparse_opposite_admissible h hl hc j)

end GeneralizedDecompositionData
end Stellmacher.Recognition.LyonsU3Four
