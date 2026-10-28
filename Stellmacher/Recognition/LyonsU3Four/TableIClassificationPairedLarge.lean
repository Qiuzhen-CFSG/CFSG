module
public import Stellmacher.Recognition.LyonsU3Four.TableIPairedLargeRows
/-!
# Canonical Table I classification for paired large differences

The paired-difference support consists of thirteen constant rows and the two
four-row orbits from Z₁ and Z₂. Normalization by the involution value preserves
Gram products and Galois multiplicities. The Gram equations force exactly one
exceptional orbit and one row `[-2,2,2,2,2,2]`. Three residual equations then
leave precisely the five multiplicity vectors A–E. Kernel-checked finite
calculations identify their full multiplicities with the actual catalogue.
The final equivalence preserves the principal row and retains every duplicate.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 377–378, Cases 2(a) and the first part of Case 3.
-/

@[expose] public section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four.TableIPairedRows
private theorem residual_solutions (a b c d e f : ℕ)
    (hb : 0 < b)
    (ht : b+c+d+4*e+4*f = 8)
    (hz : a+c+4*d+e+4*f = 8)
    (htz : c+2*d+2*e+4*f = 6) :
      (a = 0 ∧ b = 3 ∧ c = 0 ∧ d = 1 ∧ e = 0 ∧ f = 1) ∨
      (a = 1 ∧ b = 1 ∧ c = 2 ∧ d = 1 ∧ e = 1 ∧ f = 0) ∨
      (a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 0 ∧ e = 0 ∧ f = 1) ∨
      (a = 0 ∧ b = 3 ∧ c = 4 ∧ d = 1 ∧ e = 0 ∧ f = 0) ∨
      (a = 2 ∧ b = 2 ∧ c = 6 ∧ d = 0 ∧ e = 0 ∧ f = 0) := by
  have hd : d ≤ 1 := by omega
  have he : e ≤ 1 := by omega
  have hf : f ≤ 1 := by omega
  interval_cases d <;> interval_cases e <;> interval_cases f <;> omega

set_option maxHeartbeats 2000000 in
/-- The paired support and Gram identities force the multiplicities of one
of the ten actual A–E matrices, with no rows outside the support. -/
theorem count_solutions (n : Fin 21 → ℕ) (h : MultiplicityConditions n) :
    ∃ (c : TableICase) (v : c.Variant),
      (∀ a, n a = Fintype.card {j // tableIMatrix c v j = row a}) ∧
      (∀ j, ∃ a, tableIMatrix c v j = row a) := by
  have hp := h.principal_pos
  have hr1 := h.rotation_eq 13
  have hr2 := h.rotation_eq 14
  have hr3 := h.rotation_eq 15
  have hr5 := h.rotation_eq 17
  have hr6 := h.rotation_eq 18
  have hr7 := h.rotation_eq 19
  simp [rotation] at hr1 hr2 hr3 hr5 hr6 hr7
  have h00 := h.gram_eq 0 0
  have h01 := h.gram_eq 0 1
  have h02 := h.gram_eq 0 2
  have h11 := h.gram_eq 1 1
  have h12 := h.gram_eq 1 2
  have h22 := h.gram_eq 2 2
  have h23 := h.gram_eq 2 3
  simp [row, gram, Fin.sum_univ_succ] at h00 h01 h02 h11 h12 h22 h23
  have horbit : n 13 + n 17 = 1 := by omega
  have hexclude : n 0 = 0 ∧ n 1 = 0 ∧ n 2 = 0 ∧ n 4 = 0 ∧ n 5 = 0 ∧
      n 6 = 0 ∧ n 3 = 1 := by omega
  have ht : n 8+n 9+n 10+4*n 11+4*n 12 = 8 := by omega
  have hz : n 7+n 9+4*n 10+n 11+4*n 12 = 8 := by omega
  have htz : n 9+2*n 10+2*n 11+4*n 12 = 6 := by omega
  have hcases := residual_solutions (n 7) (n 8) (n 9) (n 10) (n 11) (n 12) hp ht hz htz
  have hv : (n 13 = 1 ∧ n 17 = 0) ∨ (n 13 = 0 ∧ n 17 = 1) := by omega
  clear h h00 h01 h02 h11 h12 h22 h23 ht hz htz
  rcases hv with hv | hv
  · rcases hcases with hc | hc | hc | hc | hc
    · have hn : n = ![0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0] := by
        funext a
        fin_cases a <;> dsimp <;> omega
      refine ⟨.A, .z1, ?_, ?_⟩
      · rw [hn]
        decide
      · decide
    · have hn : n = ![0, 0, 0, 1, 0, 0, 0, 1, 1, 2, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by
        funext a
        fin_cases a <;> dsimp <;> omega
      refine ⟨.B, .z1, ?_, ?_⟩
      · rw [hn]
        decide
      · decide
    · have hn : n = ![0, 0, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0] := by
        funext a
        fin_cases a <;> dsimp <;> omega
      refine ⟨.C, .z1, ?_, ?_⟩
      · rw [hn]
        decide
      · decide
    · have hn : n = ![0, 0, 0, 1, 0, 0, 0, 0, 3, 4, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by
        funext a
        fin_cases a <;> dsimp <;> omega
      refine ⟨.D, .z1, ?_, ?_⟩
      · rw [hn]
        decide
      · decide
    · have hn : n = ![0, 0, 0, 1, 0, 0, 0, 2, 2, 6, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0] := by
        funext a
        fin_cases a <;> dsimp <;> omega
      refine ⟨.E, .z1, ?_, ?_⟩
      · rw [hn]
        decide
      · decide
  · rcases hcases with hc | hc | hc | hc | hc
    · have hn : n = ![0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1] := by
        funext a
        fin_cases a <;> dsimp <;> omega
      refine ⟨.A, .z2, ?_, ?_⟩
      · rw [hn]
        decide
      · decide
    · have hn : n = ![0, 0, 0, 1, 0, 0, 0, 1, 1, 2, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1] := by
        funext a
        fin_cases a <;> dsimp <;> omega
      refine ⟨.B, .z2, ?_, ?_⟩
      · rw [hn]
        decide
      · decide
    · have hn : n = ![0, 0, 0, 1, 0, 0, 0, 2, 2, 2, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1] := by
        funext a
        fin_cases a <;> dsimp <;> omega
      refine ⟨.C, .z2, ?_, ?_⟩
      · rw [hn]
        decide
      · decide
    · have hn : n = ![0, 0, 0, 1, 0, 0, 0, 0, 3, 4, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] := by
        funext a
        fin_cases a <;> dsimp <;> omega
      refine ⟨.D, .z2, ?_, ?_⟩
      · rw [hn]
        decide
      · decide
    · have hn : n = ![0, 0, 0, 1, 0, 0, 0, 2, 2, 6, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] := by
        funext a
        fin_cases a <;> dsimp <;> omega
      refine ⟨.E, .z2, ?_, ?_⟩
      · rw [hn]
        decide
      · decide
end Stellmacher.Recognition.LyonsU3Four.TableIPairedRows

namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
variable {I : Type*} (d : GeneralizedDecompositionData I)

private theorem paired_sign_product (j : I) (x y : ℤ) :
    (d.tableIRowSign j * x) * (d.tableIRowSign j * y) = x * y := by
  calc
    _ = d.tableIRowSign j ^ 2 * (x * y) := by ring
    _ = x * y := by rw [d.tableIRowSign_sq, one_mul]

private theorem paired_sign_square (j : I) (x : ℤ) :
    (d.tableIRowSign j * x) ^ 2 = x ^ 2 := by
  simpa only [pow_two] using d.paired_sign_product j x x

private theorem paired_normalized_z (j : I) :
    TableIPairedRows.z (d.normalizedTableIRow j) = d.tableIRowSign j * d.zValue j := by
  simp only [TableIPairedRows.z, normalizedTableIRow, tableIRow_succ, zValue,
    Finset.mul_sum]

variable [Fintype I]

/-- Every normalized row in the paired branch belongs to the 21-row support. -/
theorem paired_normalized_covered {principal : I}
    (h : d.TableIPatternHypotheses principal) (hp : d.HasPairedLargeDifferences) :
    ∀ j, ∃ a, d.normalizedTableIRow j = TableIPairedRows.row a := by
  obtain ⟨_, _, hshape⟩ := d.paired_difference_support h.equation_3_2 h.galois_symmetry hp
  intro j
  obtain ⟨a, δ, k, hδ, hr⟩ := hshape j
  have hs (i : Fin 4) : d.tableIRowSign j * d.iDz i.succ j =
      d.tableIRowSign j * a + if i = k then d.tableIRowSign j * δ else 0 := by
    rw [hr]
    split_ifs <;> ring
  have hr' : d.normalizedTableIRow j =
      TableIPairedRows.shape (d.tableIRowSign j * d.dT j)
        (d.tableIRowSign j * d.iDz 0 j) (d.tableIRowSign j * a)
        (d.tableIRowSign j * δ) k := by
    funext l
    fin_cases l
    · fin_cases k <;> rfl
    · fin_cases k <;> rfl
    · have hh := hs 0; fin_cases k <;> simpa [normalizedTableIRow, tableIRow, TableIPairedRows.shape] using hh
    · have hh := hs 1; fin_cases k <;> simpa [normalizedTableIRow, tableIRow, TableIPairedRows.shape] using hh
    · have hh := hs 2; fin_cases k <;> simpa [normalizedTableIRow, tableIRow, TableIPairedRows.shape] using hh
    · have hh := hs 3; fin_cases k <;> simpa [normalizedTableIRow, tableIRow, TableIPairedRows.shape] using hh
  have hδ' : d.tableIRowSign j * δ = 0 ∨ d.tableIRowSign j * δ = 2 ∨
      d.tableIRowSign j * δ = -2 := by
    rcases sq_eq_one_iff.mp (d.tableIRowSign_sq j) with he | he <;>
      rcases hδ with rfl | rfl | rfl <;> simp [he]
  have hc : TableIPairedRows.contribution (d.normalizedTableIRow j) < 64 := by
    have hd (x y : ℤ) :
        (d.tableIRowSign j*x - d.tableIRowSign j*y)^2 = (x-y)^2 := by
      rw [← mul_sub, d.paired_sign_square]
    simpa only [TableIPairedRows.contribution, normalizedTableIRow, tableIRow_zero,
      tableIRow_succ, d.paired_sign_square, hd, contribution] using h.equation_3_3 j
  have hm : Int.ModEq 4 (d.tableIRowSign j * d.dT j)
      (TableIPairedRows.z (d.normalizedTableIRow j)) := by
    rw [d.paired_normalized_z]
    exact (h.equation_3_4 j).mul_left (d.tableIRowSign j)
  have hz : 0 < TableIPairedRows.z (d.normalizedTableIRow j) := by
    rw [d.paired_normalized_z]
    have hn := h.z_nonzero j
    unfold tableIRowSign
    split <;> simp only [one_mul, neg_one_mul] <;> omega
  rw [hr'] at hc hm hz ⊢
  exact TableIPairedRows.shape_covered _ _ _ _ _ hδ' hc hm hz
/-- Row signs cancel in every Gram entry. -/
theorem paired_normalized_gram {principal : I}
    (h : d.TableIPatternHypotheses principal) (k l : Fin 6) :
    ∑ j, d.normalizedTableIRow j k * d.normalizedTableIRow j l =
      TableIPairedRows.gram k l := by
  simp only [normalizedTableIRow, d.paired_sign_product]
  refine Fin.cases ?_ (fun a => ?_) k
  · refine Fin.cases ?_ (fun b => ?_) l
    · exact h.equation_3_2.tt
    · simpa [TableIPairedRows.gram, columnInner] using h.equation_3_2.tz b
  · refine Fin.cases ?_ (fun b => ?_) l
    · simpa [TableIPairedRows.gram, columnInner, mul_comm] using h.equation_3_2.tz a
    · simpa [TableIPairedRows.gram, columnInner] using h.equation_3_2.zz a b

/-- Normalization commutes with the Galois permutation. -/
theorem paired_normalized_galois {principal : I}
    (h : d.TableIPatternHypotheses principal) :
    ∃ σ : Equiv.Perm I, ∀ j,
      d.normalizedTableIRow j = TableIPairedRows.rotate (d.normalizedTableIRow (σ j)) := by
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
theorem paired_multiplicity_rotate {principal : I}
    (h : d.TableIPatternHypotheses principal) (r : TableIRow) :
    d.tableIRowMultiplicity (TableIPairedRows.rotate r) = d.tableIRowMultiplicity r := by
  classical
  obtain ⟨σ, hσ⟩ := d.paired_normalized_galois h
  exact Fintype.card_congr (σ.subtypeEquiv (fun j => by
    change d.normalizedTableIRow j = TableIPairedRows.rotate r ↔
      d.normalizedTableIRow (σ j) = r
    rw [hσ j]
    exact TableIPairedRows.rotate_injective.eq_iff))

/-- Sum any statistic on a covered matrix by full row multiplicities. -/
theorem paired_sum_by_multiplicity
    (hcover : ∀ j, ∃ a, d.normalizedTableIRow j = TableIPairedRows.row a)
    (f : TableIRow → ℤ) :
    ∑ a, (d.tableIRowMultiplicity (TableIPairedRows.row a) : ℤ) *
      f (TableIPairedRows.row a) = ∑ j, f (d.normalizedTableIRow j) := by
  classical
  have hn (a : Fin 21) : (d.tableIRowMultiplicity (TableIPairedRows.row a) : ℤ) =
      ∑ j, if d.normalizedTableIRow j = TableIPairedRows.row a then 1 else 0 := by
    rw [tableIRowMultiplicity, Fintype.card_subtype, Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [hn, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨a, ha⟩ := hcover j
  have he (b : Fin 21) : d.normalizedTableIRow j = TableIPairedRows.row b ↔ b = a := by
    rw [ha]
    exact TableIPairedRows.row_injective.eq_iff.trans eq_comm
  simp only [he]
  simp [ha]

/-- Coverage turns the ambient numerical hypotheses into a finite count system. -/
theorem paired_multiplicity_conditions {principal : I}
    (h : d.TableIPatternHypotheses principal)
    (hcover : ∀ j, ∃ a, d.normalizedTableIRow j = TableIPairedRows.row a) :
    TableIPairedRows.MultiplicityConditions
      (fun a => d.tableIRowMultiplicity (TableIPairedRows.row a)) := by
  classical
  constructor
  · apply Fintype.card_pos_iff.mpr
    exact ⟨⟨principal, (d.normalizedTableIRow_principal principal h).trans
      (show TableIPairedRows.row 8 = ![1,1,0,0,0,0] from rfl).symm⟩⟩
  · intro a
    rw [TableIPairedRows.row_rotation]
    exact d.paired_multiplicity_rotate h _
  · intro k l
    simpa only [mul_assoc] using
      (d.paired_sum_by_multiplicity hcover (fun r => r k * r l)).trans
        (d.paired_normalized_gram h k l)

/-- Paired large adjacent differences give exactly the canonical A–E matrices,
with either of their two valid initial blocks and every duplicate retained. -/
theorem hasCanonicalTableIPattern_of_pairedLargeDifferences (principal : I)
    (h : d.TableIPatternHypotheses principal) (hp : d.HasPairedLargeDifferences) :
    d.HasCanonicalTableIPattern principal := by
  classical
  have hcover := d.paired_normalized_covered h hp
  obtain ⟨c, v, hm, hv⟩ := TableIPairedRows.count_solutions _
    (d.paired_multiplicity_conditions h hcover)
  apply d.hasCanonicalTableIPattern_of_rowMultiplicity principal h c v
  intro r
  by_cases hr : ∃ a, TableIPairedRows.row a = r
  · obtain ⟨a, rfl⟩ := hr
    exact hm a
  · have hz : d.tableIRowMultiplicity r = 0 := by
      unfold tableIRowMultiplicity
      apply Fintype.card_eq_zero_iff.mpr
      refine ⟨fun j => ?_⟩
      obtain ⟨a, ha⟩ := hcover j.1
      exact hr ⟨a, ha.symm.trans j.2⟩
    rw [hz]
    symm
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun j => ?_⟩
    obtain ⟨a, ha⟩ := hv j.1
    exact hr ⟨a, ha.symm.trans j.2⟩

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
