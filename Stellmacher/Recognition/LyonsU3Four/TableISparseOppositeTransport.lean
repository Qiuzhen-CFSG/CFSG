module

public import Stellmacher.Recognition.LyonsU3Four.TableISparseOppositeRows

/-!
# Transport of sparse opposite-pair row counts

Galois symmetry identifies the fibers of rotated normalized rows. Regrouping
Gram sums over disjoint catalogue orbits gives the integer count constraints,
while equality with a model's counts reconstructs a principal-preserving signed
row equivalence. All fibers retain repeated rows.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
Table I and pp. 379–380.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
open scoped BigOperators
open SparseOppositeRows

variable {I : Type*} [Fintype I] (d : GeneralizedDecompositionData I)

private theorem opposite_rotate_injective : Function.Injective rotate := by
  intro r s he
  funext k
  fin_cases k
  · exact congrFun he 0
  · exact congrFun he 1
  · exact congrFun he 3
  · exact congrFun he 4
  · exact congrFun he 5
  · exact congrFun he 2

/-- Normalization commutes with the Galois permutation. -/
private theorem opposite_normalized_galois {principal : I}
    (h : d.TableIPatternHypotheses principal) :
    ∃ σ : Equiv.Perm I, ∀ j,
      d.normalizedTableIRow j = SparseOppositeRows.rotate (d.normalizedTableIRow (σ j)) := by
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
theorem opposite_multiplicity_rotate {principal : I}
    (h : d.TableIPatternHypotheses principal) (r : TableIRow) :
    d.tableIRowMultiplicity (SparseOppositeRows.rotate r) = d.tableIRowMultiplicity r := by
  classical
  obtain ⟨σ, hσ⟩ := d.opposite_normalized_galois h
  exact Fintype.card_congr (σ.subtypeEquiv (fun j => by
    change d.normalizedTableIRow j = SparseOppositeRows.rotate r ↔
      d.normalizedTableIRow (σ j) = r
    rw [hσ j]
    exact opposite_rotate_injective.eq_iff))

/-- Counts are constant on every catalogue orbit. -/
theorem opposite_multiplicity_rotation {principal : I}
    (h : d.TableIPatternHypotheses principal) (r : TableIRow) (k : Fin 4) :
    d.tableIRowMultiplicity (rotation r k) = d.tableIRowMultiplicity r := by
  fin_cases k <;> simp [rotation, d.opposite_multiplicity_rotate h]

private theorem opposite_multiplicity_mem {principal : I}
    (h : d.TableIPatternHypotheses principal) {p : Fin 51} {r : TableIRow}
    (hr : r ∈ orbit p) :
    d.tableIRowMultiplicity r = d.tableIRowMultiplicity (representative p) := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
  exact d.opposite_multiplicity_rotation h _ k

private theorem opposite_sum_by_multiplicity
    (hs : ∀ j, ∃ p, d.normalizedTableIRow j ∈ orbit p) (f : TableIRow → ℤ) :
    ∑ p, ∑ r ∈ orbit p, (d.tableIRowMultiplicity r : ℤ) * f r =
      ∑ j, f (d.normalizedTableIRow j) := by
  classical
  have hn (r : TableIRow) : (d.tableIRowMultiplicity r : ℤ) =
      ∑ j, if d.normalizedTableIRow j = r then 1 else 0 := by
    rw [tableIRowMultiplicity, Fintype.card_subtype, Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [hn, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  conv_lhs => arg 2; ext p; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨p, hp⟩ := hs j
  rw [Finset.sum_eq_single p]
  · exact Finset.sum_ite_eq (orbit p) (d.normalizedTableIRow j) f |>.trans (if_pos hp)
  · intro q _ hq
    have hnq : d.normalizedTableIRow j ∉ orbit q := by
      intro hq'
      exact Finset.disjoint_left.mp (orbit_disjoint p q (Ne.symm hq)) hp hq'
    simp [Finset.sum_ite_eq, hnq]
  · simp

private theorem opposite_normalized_gram {principal : I}
    (h : d.TableIPatternHypotheses principal) (i : Fin 8) :
    ∑ j, d.normalizedTableIRow j (gramPairs i).1 *
      d.normalizedTableIRow j (gramPairs i).2 = gramValue i := by
  have hs (j : I) (a b : ℤ) :
      d.tableIRowSign j * a * (d.tableIRowSign j * b) = a * b := by
    calc
      _ = d.tableIRowSign j ^ 2 * (a * b) := by ring
      _ = a * b := by rw [d.tableIRowSign_sq, one_mul]
  simp only [normalizedTableIRow, hs]
  fin_cases i
  · exact h.equation_3_2.tt
  · exact h.equation_3_2.tz 0
  · exact h.equation_3_2.tz 1
  · exact h.equation_3_2.zz 0 0
  · exact h.equation_3_2.zz 0 1
  · exact h.equation_3_2.zz 1 1
  · exact h.equation_3_2.zz 1 2
  · exact h.equation_3_2.zz 1 3

/-- Support and Galois symmetry transport the ambient hypotheses to the full
orbit multiplicity system. -/
theorem opposite_multiplicity_constraints {principal : I}
    (h : d.TableIPatternHypotheses principal)
    (hs : ∀ j, ∃ p, d.normalizedTableIRow j ∈ orbit p)
    (ho : d.HasOppositeUnitDifferences) :
    MultiplicityConstraints (fun p => d.tableIRowMultiplicity (representative p)) := by
  classical
  constructor
  · intro i
    calc
      _ = ∑ p, ∑ r ∈ orbit p, (d.tableIRowMultiplicity r : ℤ) *
          (r (gramPairs i).1 * r (gramPairs i).2) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [← moment_eq, moment, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        rw [d.opposite_multiplicity_mem h hr]
      _ = _ := (d.opposite_sum_by_multiplicity hs _).trans
        (d.opposite_normalized_gram h i)
  · change 0 < Fintype.card {j // d.normalizedTableIRow j = representative 34}
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨principal, d.normalizedTableIRow_principal principal h⟩⟩
  · obtain ⟨j, hj⟩ := ho
    obtain ⟨p, hp⟩ := hs j
    have hd (i : Fin 4) : difference (d.normalizedTableIRow j) i =
        d.tableIRowSign j * d.adjacentDifference i j := by
      fin_cases i <;> simp [difference, normalizedTableIRow, tableIRow,
        adjacentDifference, mul_sub]
    have hj' : difference (d.normalizedTableIRow j) = ![1, 0, -1, 0] ∨
        difference (d.normalizedTableIRow j) = ![-1, 0, 1, 0] := by
      rcases sq_eq_one_iff.mp (d.tableIRowSign_sq j) with hsign | hsign
      · simpa only [funext hd, hsign, one_mul] using hj
      · rcases hj with hj | hj
        · right
          funext i
          rw [hd, hsign, congrFun hj i]
          fin_cases i <;> decide
        · left
          funext i
          rw [hd, hsign, congrFun hj i]
          fin_cases i <;> decide
    have hpo : p ∈ oppositeOrbits := by
      apply (opposite_iff p).mpr
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hp
      exact ⟨k, hk.symm ▸ hj'⟩
    have hpos : 0 < d.tableIRowMultiplicity (representative p) := by
      rw [← d.opposite_multiplicity_mem h hp]
      exact Fintype.card_pos_iff.mpr ⟨⟨j, rfl⟩⟩
    exact le_trans hpos (Finset.single_le_sum
      (f := fun p => d.tableIRowMultiplicity (representative p))
      (fun _ _ => Nat.zero_le _) hpo)

/-- Equality with any one of the four model count vectors reconstructs the
canonical signed matrix, including repeated rows and the principal index. -/
theorem hasCanonicalTableIPattern_of_opposite_modelCounts {principal : I}
    (h : d.TableIPatternHypotheses principal)
    (hs : ∀ j, ∃ p, d.normalizedTableIRow j ∈ orbit p)
    (v : Fin 4)
    (hm : (fun p => d.tableIRowMultiplicity (representative p)) = modelCounts v) :
    d.HasCanonicalTableIPattern principal := by
  classical
  apply d.hasCanonicalTableIPattern_of_rowMultiplicity principal h (modelCase v) (modelVariant v)
  intro r
  by_cases hr : ∃ p, r ∈ orbit p
  · obtain ⟨p, hp⟩ := hr
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
    rw [d.opposite_multiplicity_rotation h, congrFun hm p]
    exact modelCounts_rotation_eq v p k
  · have ha : IsEmpty {j // d.normalizedTableIRow j = r} := ⟨by
      rintro ⟨j, rfl⟩
      exact hr (hs j)⟩
    have hb : IsEmpty {j // tableIMatrix (modelCase v) (modelVariant v) j = r} := ⟨by
      rintro ⟨j, rfl⟩
      exact hr (model_supported v j)⟩
    simp only [tableIRowMultiplicity, Fintype.card_eq_zero]

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
