module

public import Stellmacher.Recognition.LyonsU3Four.TableIDifferenceColumns
public import Stellmacher.Recognition.LyonsU3Four.TableIRowMultiplicity
public import Stellmacher.Recognition.LyonsU3Four.TableIColumnReflection
public import Stellmacher.Recognition.LyonsU3Four.TableISparseRowCoverage
public import Stellmacher.Recognition.LyonsU3Four.TableISparseMultiplicityClassification

/-!
# Assembly for the sparse branch without opposite unit differences

Normalize signs by the nonzero involution value. This preserves the local
contribution bound, congruence, Gram matrix, and Galois row permutation. Given
coverage by the explicit sparse row list, the full multiplicity vector satisfies
a finite integer system. Exact classification of that system then supplies the
principal-preserving signed equivalence with a canonical Table I matrix.

The arithmetic certificates establish local row coverage and multiplicity
classification into M, N, P, Q, R. The assembly below transports these results
to arbitrary finite row types, retaining duplicate rows and the principal row.
This branch already has a canonical pattern without reflecting the columns.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 379–380, Table II and Case 6(a),(b).
-/

@[expose] public section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
variable {I : Type*} (d : GeneralizedDecompositionData I)

private theorem sign_product (j : I) (x y : ℤ) :
    (d.tableIRowSign j * x) * (d.tableIRowSign j * y) = x * y := by
  calc
    _ = d.tableIRowSign j ^ 2 * (x * y) := by ring
    _ = x * y := by rw [d.tableIRowSign_sq, one_mul]

private theorem sign_square (j : I) (x : ℤ) :
    (d.tableIRowSign j * x) ^ 2 = x ^ 2 := by
  simpa only [pow_two] using d.sign_product j x x

private theorem normalized_z (j : I) :
    TableISparseRows.z (d.normalizedTableIRow j) = d.tableIRowSign j * d.zValue j := by
  simp only [TableISparseRows.z, normalizedTableIRow, tableIRow_succ, zValue,
    Finset.mul_sum]

private theorem normalized_difference (j : I) (i : Fin 4) :
    TableISparseRows.difference (d.normalizedTableIRow j) i =
      d.tableIRowSign j * d.adjacentDifference i j := by
  fin_cases i <;> simp [TableISparseRows.difference, normalizedTableIRow,
    adjacentDifference, tableIRow] <;> ring

variable [Fintype I]

/-- Sign normalization preserves the local sparse numerical conditions. -/
theorem normalized_sparse_admissible {principal : I}
    (h : d.TableIPatternHypotheses principal)
    (hl : ¬ d.HasLargeDifference) (hc : ¬ d.HasConsecutiveUnitDifferences)
    (ho : ¬ d.HasOppositeUnitDifferences) (j : I) :
    TableISparseRows.Admissible (d.normalizedTableIRow j) := by
  have hd (x y : ℤ) :
      (d.tableIRowSign j * x - d.tableIRowSign j * y) ^ 2 = (x - y) ^ 2 := by
    rw [← mul_sub, d.sign_square]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [TableISparseRows.contribution, normalizedTableIRow, tableIRow_zero,
      tableIRow_succ, d.sign_square, hd, contribution] using h.equation_3_3 j
  · rw [d.normalized_z]
    exact (h.equation_3_4 j).mul_left (d.tableIRowSign j)
  · rw [d.normalized_z]
    have hn := h.z_nonzero j
    unfold tableIRowSign
    split <;> simp only [one_mul, neg_one_mul] <;> omega
  · intro i
    rw [d.normalized_difference]
    have hb := h.equation_3_2.unit_bounds_of_not_large d hl i j
    rcases sq_eq_one_iff.mp (d.tableIRowSign_sq j) with hs | hs
    · simpa only [hs, one_mul] using hb
    · rw [hs, neg_one_mul]
      omega
  · simp only [d.normalized_difference, d.sign_product]
    exact d.sparse_opposite_products h hl hc ho j

/-- Row signs cancel in every Gram entry. -/
theorem normalized_tableI_gram {principal : I}
    (h : d.TableIPatternHypotheses principal) (k l : Fin 6) :
    ∑ j, d.normalizedTableIRow j k * d.normalizedTableIRow j l =
      TableISparseRows.gram k l := by
  simp only [normalizedTableIRow, d.sign_product]
  refine Fin.cases ?_ (fun a => ?_) k
  · refine Fin.cases ?_ (fun b => ?_) l
    · exact h.equation_3_2.tt
    · simpa [TableISparseRows.gram, columnInner] using h.equation_3_2.tz b
  · refine Fin.cases ?_ (fun b => ?_) l
    · simpa [TableISparseRows.gram, columnInner, mul_comm] using h.equation_3_2.tz a
    · simpa [TableISparseRows.gram, columnInner] using h.equation_3_2.zz a b

/-- Normalization commutes with the Galois permutation. -/
theorem normalized_tableI_galois {principal : I}
    (h : d.TableIPatternHypotheses principal) :
    ∃ σ : Equiv.Perm I, ∀ j,
      d.normalizedTableIRow j = TableISparseRows.rotate (d.normalizedTableIRow (σ j)) := by
  obtain ⟨σ, hσ⟩ := h.galois_symmetry
  have hz (j : I) : d.zValue j = d.zValue (σ j) := by
    simp [zValue, Fin.sum_univ_succ]
    rw [(hσ j).2 0, (hσ j).2 1, (hσ j).2 2, (hσ j).2 3, (hσ j).2 4]
    simp only [show galoisColumn 0 = 0 from rfl,
      show galoisColumn 1 = 4 from rfl, show galoisColumn 2 = 1 from rfl,
      show galoisColumn 3 = 2 from rfl, show galoisColumn 4 = 3 from rfl]
    ring
  have hs (j : I) : d.tableIRowSign j = d.tableIRowSign (σ j) := by
    simp only [tableIRowSign, hz j]
  refine ⟨σ, fun j => ?_⟩
  funext k
  fin_cases k
  · exact congrArg₂ (· * ·) (hs j) (hσ j).1
  · exact congrArg₂ (· * ·) (hs j) ((hσ j).2 0)
  · exact congrArg₂ (· * ·) (hs j) ((hσ j).2 1)
  · exact congrArg₂ (· * ·) (hs j) ((hσ j).2 2)
  · exact congrArg₂ (· * ·) (hs j) ((hσ j).2 3)
  · exact congrArg₂ (· * ·) (hs j) ((hσ j).2 4)

/-- Galois rotation preserves the multiplicity of every normalized row. -/
theorem sparse_multiplicity_rotate {principal : I}
    (h : d.TableIPatternHypotheses principal) (r : TableIRow) :
    d.tableIRowMultiplicity (TableISparseRows.rotate r) = d.tableIRowMultiplicity r := by
  classical
  obtain ⟨σ, hσ⟩ := d.normalized_tableI_galois h
  exact Fintype.card_congr (σ.subtypeEquiv (fun j => by
    change d.normalizedTableIRow j = TableISparseRows.rotate r ↔
      d.normalizedTableIRow (σ j) = r
    rw [hσ j]
    exact TableISparseRows.rotate_injective.eq_iff))

/-- Sum any statistic on a covered matrix by full row multiplicities. -/
theorem sparse_sum_by_multiplicity
    (hcover : ∀ j, ∃ a, d.normalizedTableIRow j = TableISparseRows.row a)
    (f : TableIRow → ℤ) :
    ∑ a, (d.tableIRowMultiplicity (TableISparseRows.row a) : ℤ) *
      f (TableISparseRows.row a) = ∑ j, f (d.normalizedTableIRow j) := by
  classical
  have hn (a : Fin 85) : (d.tableIRowMultiplicity (TableISparseRows.row a) : ℤ) =
      ∑ j, if d.normalizedTableIRow j = TableISparseRows.row a then 1 else 0 := by
    rw [tableIRowMultiplicity, Fintype.card_subtype, Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [hn, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨a, ha⟩ := hcover j
  have he (b : Fin 85) : d.normalizedTableIRow j = TableISparseRows.row b ↔ b = a := by
    rw [ha]
    exact TableISparseRows.row_injective.eq_iff.trans eq_comm
  simp only [he]
  simp [ha]

/-- Coverage turns the ambient numerical hypotheses into a finite count system. -/
theorem sparse_multiplicity_conditions {principal : I}
    (h : d.TableIPatternHypotheses principal)
    (hcover : ∀ j, ∃ a, d.normalizedTableIRow j = TableISparseRows.row a) :
    TableISparseRows.MultiplicityConditions
      (fun a => d.tableIRowMultiplicity (TableISparseRows.row a)) := by
  classical
  constructor
  · apply Fintype.card_pos_iff.mpr
    exact ⟨⟨principal, (d.normalizedTableIRow_principal principal h).trans
      TableISparseRows.row_principal.symm⟩⟩
  · intro a
    rw [TableISparseRows.row_rotation]
    exact d.sparse_multiplicity_rotate h _
  · intro k l
    simpa only [mul_assoc] using
      (d.sparse_sum_by_multiplicity hcover (fun r => r k * r l)).trans
        (d.normalized_tableI_gram h k l)

/-- Reconstruct all row multiplicities, including zeros outside the candidate list. -/
theorem sparse_multiplicity_reconstruct
    (hcover : ∀ j, ∃ a, d.normalizedTableIRow j = TableISparseRows.row a) (r : TableIRow) :
    (∑ a, if TableISparseRows.row a = r then
      d.tableIRowMultiplicity (TableISparseRows.row a) else 0) =
      d.tableIRowMultiplicity r := by
  classical
  have hsum := d.sparse_sum_by_multiplicity hcover
    (fun s => if s = r then 1 else 0)
  have hr : (d.tableIRowMultiplicity r : ℤ) =
      ∑ j, if d.normalizedTableIRow j = r then 1 else 0 := by
    rw [tableIRowMultiplicity, Fintype.card_subtype, Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← hr] at hsum
  have : ((∑ a, if TableISparseRows.row a = r then
      d.tableIRowMultiplicity (TableISparseRows.row a) else 0) : ℤ) =
      d.tableIRowMultiplicity r := by
    simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, mul_ite,
      mul_one, mul_zero] using hsum
  exact_mod_cast this

/-- Assembly of the sparse branch from its two finite arithmetic certificates.
The hypotheses are respectively local row coverage and exact classification of
nonnegative integer multiplicities; neither drops duplicate ambient rows. -/
theorem hasCanonicalTableIPattern_of_sparse_certificates {principal : I}
    (h : d.TableIPatternHypotheses principal)
    (hl : ¬ d.HasLargeDifference) (hc : ¬ d.HasConsecutiveUnitDifferences)
    (ho : ¬ d.HasOppositeUnitDifferences)
    (coverage : ∀ r, TableISparseRows.Admissible r → ∃ a, r = TableISparseRows.row a)
    (counts : ∀ n : Fin 85 → ℕ, TableISparseRows.MultiplicityConditions n →
      ∃ (c : TableICase) (v : c.Variant), ∀ r,
        (∑ a, if TableISparseRows.row a = r then n a else 0) =
          Fintype.card {j // tableIMatrix c v j = r}) :
    d.HasCanonicalTableIPattern principal := by
  classical
  have hcover (j : I) : ∃ a, d.normalizedTableIRow j = TableISparseRows.row a :=
    coverage _ (d.normalized_sparse_admissible h hl hc ho j)
  obtain ⟨c, v, hv⟩ := counts _ (d.sparse_multiplicity_conditions h hcover)
  apply d.hasCanonicalTableIPattern_of_rowMultiplicity principal h c v
  intro r
  rw [← d.sparse_multiplicity_reconstruct hcover r]
  exact hv r

/-- The sparse branch without opposite unit differences has a canonical
Table I pattern, with every row multiplicity and the principal row preserved. -/
theorem hasCanonicalTableIPattern_of_sparse_without_opposite {principal : I}
    (h : d.TableIPatternHypotheses principal)
    (hl : ¬ d.HasLargeDifference) (hc : ¬ d.HasConsecutiveUnitDifferences)
    (ho : ¬ d.HasOppositeUnitDifferences) :
    d.HasCanonicalTableIPattern principal :=
  d.hasCanonicalTableIPattern_of_sparse_certificates h hl hc ho
    TableISparseRows.admissible_covered TableISparseRows.multiplicities_classified

/-- The sparse branch without an opposite pair closes the corresponding case
of Table I classification up to column reflection. -/
theorem canonical_or_reflected_of_sparse_without_opposite {principal : I}
    (h : d.TableIPatternHypotheses principal)
    (hl : ¬ d.HasLargeDifference) (hc : ¬ d.HasConsecutiveUnitDifferences)
    (ho : ¬ d.HasOppositeUnitDifferences) :
    d.HasCanonicalTableIPattern principal ∨
      d.reflectColumns.HasCanonicalTableIPattern principal :=
  Or.inl (d.hasCanonicalTableIPattern_of_sparse_without_opposite h hl hc ho)

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
