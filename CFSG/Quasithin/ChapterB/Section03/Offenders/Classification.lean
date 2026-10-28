module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Generated
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Ratios

/-!
# The exhaustive offender classification in degrees five through eight

This assembles the orbit, subgroup-lattice, and fixed-space calculations into
uniform statements for all four binary permutation sections. Case (a) consists
exactly of the disjoint-transposition groups and their conjugates. Case (b)
adds the exceptional group, the even part of `D`, and every other hyperplane.
Only the degree-eight natural module has the further regular elementary-eight
family. The fixed codimensions and quadratic ratios retain these distinctions.

The degree-six exports also give the fourteen-member Sylow list, the unique
strong offender, the even offender family, and the equal-weight inclusions
used in B.3.4. All degree-specific premises have been discharged.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(1)–(6), printed pp. 83–84.
-/

public section
namespace CFSG.Quasithin.ChapterB.Offenders
open BinaryPermutation Representation.BinaryOffender
open scoped ENNReal

/-- B.3.2(1): ranks and all four fixed codimensions. -/
theorem disjointTranspositions_dimensions {n m : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) (hm : 1 ≤ m) (hmn : m ≤ n / 2) :
    rank (disjointTranspositions n m) = m ∧
    fixedCodim (representation (Fin n)) (disjointTranspositions n m) = m ∧
    fixedCodim (deletedRepresentation (Fin n)) (disjointTranspositions n m) = m ∧
    fixedCodim (coreRepresentation (Fin n)) (disjointTranspositions n m) =
      (if Even n ∧ m = n / 2 then m - 1 else m) ∧
    fixedCodim (naturalRepresentation (Fin n)) (disjointTranspositions n m) =
      (if Even n ∧ m = n / 2 then m - 1 else m) := by
  by_cases ho : n = 5 ∨ n = 7
  · have he : ¬ Even n := by rcases ho with rfl | rfl <;> decide
    simp only [he, false_and, ite_false]
    exact ⟨Odd.rank_disjointTranspositions ho hmn,
      Odd.fixedCodim_full_disjointTranspositions ho hmn,
      Odd.fixedCodim_deleted_disjointTranspositions ho hmn,
      Odd.fixedCodim_core_disjointTranspositions ho hmn,
      Odd.fixedCodim_natural_disjointTranspositions ho hmn⟩
  · have hn : n = 6 ∨ n = 8 := by omega
    rcases hn with rfl | rfl
    · have hmn : m ≤ 3 := hmn
      interval_cases m
      · simpa [Nat.even_iff] using (show rank (disjointTranspositions 6 1) = 1 ∧ _ from
          ⟨Six.rank_A1, Six.fixedCodim_A1⟩)
      · simpa [Nat.even_iff] using (show rank (disjointTranspositions 6 2) = 2 ∧ _ from
          ⟨Six.rank_A2, Six.fixedCodim_A2⟩)
      · simpa [Nat.even_iff] using (show rank (D 6) = 3 ∧ _ from ⟨Six.rank_D, Six.fixedCodim_D⟩)
    · have hmn : m ≤ 4 := hmn
      refine ⟨Eight.rank_disjointTranspositions ⟨m, by omega⟩, ?_⟩
      have h := Eight.fixedCodim_disjointTranspositions hm hmn
      interval_cases m <;> simpa [Nat.even_iff] using h

/-- B.3.2(2): the exceptional group on both case-(b) sections. -/
theorem exceptional_dimensions {n : ℕ} (hn : n = 6 ∨ n = 8) :
    rank (exceptional n (by omega)) = n / 2 ∧
    fixedCodim (coreRepresentation (Fin n)) (exceptional n (by omega)) = n / 2 ∧
    fixedCodim (naturalRepresentation (Fin n)) (exceptional n (by omega)) = n / 2 := by
  rcases hn with rfl | rfl
  · exact ⟨Six.rank_exceptional, Six.fixedCodim_exceptional.2.2⟩
  · exact Eight.exceptional_rank_codim

/-- Every hyperplane, including the even part, has the indicated dimensions. -/
theorem hyperplane_dimensions {n : ℕ} (hn : n = 6 ∨ n = 8)
    {H : Subgroup (Equiv.Perm (Fin n))} (hH : H ⋖ D n) :
    rank H = n / 2 - 1 ∧
    fixedCodim (coreRepresentation (Fin n)) H = n / 2 - 1 ∧
    fixedCodim (naturalRepresentation (Fin n)) H = n / 2 - 1 := by
  rcases hn with rfl | rfl
  · have h := Six.hyperplane_dimensions hH
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · exact ⟨Eight.rank_hyperplane hH, Eight.fixedCodim_hyperplane hH⟩

/-- B.3.2(4), uniformly on the full permutation module. -/
theorem isBestOffender_full_iff {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (A : Subgroup (Equiv.Perm (Fin n))) :
    IsBestOffender (representation (Fin n)) A ↔ CaseAFamily n A := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact Odd.isBestOffender_full_iff_caseAFamily (Or.inl rfl) A
  · exact Six.isBestOffender_full_iff A
  · exact Odd.isBestOffender_full_iff_caseAFamily (Or.inr rfl) A
  · exact Eight.isBestOffender_full_iff A

/-- B.3.2(4), uniformly on the quotient by the constant line. -/
theorem isBestOffender_deleted_iff {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (A : Subgroup (Equiv.Perm (Fin n))) :
    IsBestOffender (deletedRepresentation (Fin n)) A ↔ CaseAFamily n A := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact Odd.isBestOffender_deleted_iff_caseAFamily (Or.inl rfl) A
  · exact Six.isBestOffender_deleted_iff A
  · exact Odd.isBestOffender_deleted_iff_caseAFamily (Or.inr rfl) A
  · exact Eight.isBestOffender_deleted_iff A

/-- B.3.2(4),(5), retaining every hyperplane in even degree. -/
theorem isBestOffender_core_iff {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (A : Subgroup (Equiv.Perm (Fin n))) :
    IsBestOffender (coreRepresentation (Fin n)) A ↔
      if Even n then CaseBFamily n (by omega) A else CaseAFamily n A := by
  rcases hn with rfl | rfl | rfl | rfl
  · simpa [Nat.even_iff] using Odd.isBestOffender_core_iff_caseAFamily (Or.inl rfl) A
  · simpa [Nat.even_iff] using Six.isBestOffender_core_iff A
  · simpa [Nat.even_iff] using Odd.isBestOffender_core_iff_caseAFamily (Or.inr rfl) A
  · simpa [Nat.even_iff] using Eight.isBestOffender_core_iff A

/-- B.3.2(4)–(6): the regular family occurs exactly for the degree-eight natural module. -/
theorem isBestOffender_natural_iff {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (A : Subgroup (Equiv.Perm (Fin n))) :
    IsBestOffender (naturalRepresentation (Fin n)) A ↔
      (if Even n then CaseBFamily n (by omega) A else CaseAFamily n A) ∨
        ∃ h : n = 8, IsRegularEight (h ▸ A) := by
  rcases hn with rfl | rfl | rfl | rfl
  · simpa [Nat.even_iff] using Odd.isBestOffender_natural_iff_caseAFamily (Or.inl rfl) A
  · simpa [Nat.even_iff] using Six.isBestOffender_natural_iff A
  · simpa [Nat.even_iff] using Odd.isBestOffender_natural_iff_caseAFamily (Or.inr rfl) A
  · simpa [Nat.even_iff] using Eight.isBestOffender_natural_iff A

/-- All four global action ratios, with precisely the source's parity distinction. -/
theorem quadraticRatios {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    quadraticRatio (representation (Fin n)) = 1 ∧
    quadraticRatio (deletedRepresentation (Fin n)) = 1 ∧
    quadraticRatio (coreRepresentation (Fin n)) =
      (if Even n then ((n - 2 : ℕ) : ℝ≥0∞) / n else 1) ∧
    quadraticRatio (naturalRepresentation (Fin n)) =
      (if Even n then ((n - 2 : ℕ) : ℝ≥0∞) / n else 1) := by
  rcases hn with rfl | rfl | rfl | rfl
  · simpa [Nat.even_iff] using Odd.quadraticRatios (Or.inl rfl : 5 = 5 ∨ 5 = 7)
  · simp only [Six.quadraticRatio_full, Six.quadraticRatio_deleted,
      Six.quadraticRatio_core, Six.quadraticRatio_natural, true_and]
    norm_num [Nat.even_iff]
    rw [ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)]
    norm_num
  · simpa [Nat.even_iff] using Odd.quadraticRatios (Or.inr rfl : 7 = 5 ∨ 7 = 7)
  · simp only [Eight.quadraticRatio_full, Eight.quadraticRatio_deleted,
      Eight.quadraticRatio_core, Eight.quadraticRatio_natural, true_and]
    norm_num [Nat.even_iff]
    rw [ENNReal.div_eq_div_iff (by norm_num) (by simp) (by norm_num) (by simp)]
    norm_num

/-- B.3.2(3): the regular degree-eight subgroup has rank and natural codimension three. -/
theorem regularEight_dimensions {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) :
    rank A = 3 ∧ fixedCodim (naturalRepresentation (Fin 8)) A = 3 :=
  ⟨rank_eq_three_of_isRegularEight hA, fixedCodim_natural_regularEight hA⟩

/-- No strong offender occurs on the full module in any of the four degrees. -/
theorem not_isStrongOffender_full {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (A : Subgroup (Equiv.Perm (Fin n))) : ¬ IsStrongOffender (representation (Fin n)) A := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact Odd.not_isStrongOffender_full (Or.inl rfl) A
  · exact Six.not_isStrongOffender_full A
  · exact Odd.not_isStrongOffender_full (Or.inr rfl) A
  · exact Eight.not_isStrongOffender_full A

/-- No strong offender occurs on the deleted module in any of the four degrees. -/
theorem not_isStrongOffender_deleted {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (A : Subgroup (Equiv.Perm (Fin n))) : ¬ IsStrongOffender (deletedRepresentation (Fin n)) A := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact Odd.not_isStrongOffender_deleted (Or.inl rfl) A
  · exact Six.not_isStrongOffender_deleted A
  · exact Odd.not_isStrongOffender_deleted (Or.inr rfl) A
  · exact Eight.not_isStrongOffender_deleted A

/-- In even degree, the strong core offenders are precisely the conjugates of `D`. -/
theorem isStrongOffender_core_iff {n : ℕ} (hn : n = 6 ∨ n = 8)
    (A : Subgroup (Equiv.Perm (Fin n))) :
    IsStrongOffender (coreRepresentation (Fin n)) A ↔ IsConjugateTo A (D n) := by
  rcases hn with rfl | rfl
  · exact Six.isStrongOffender_core_iff A
  · exact Eight.isStrongOffender_core_iff A

/-- The degree-eight regular exception introduces no additional strong offenders. -/
theorem isStrongOffender_natural_iff {n : ℕ} (hn : n = 6 ∨ n = 8)
    (A : Subgroup (Equiv.Perm (Fin n))) :
    IsStrongOffender (naturalRepresentation (Fin n)) A ↔ IsConjugateTo A (D n) := by
  rcases hn with rfl | rfl
  · exact Six.isStrongOffender_natural_iff A
  · exact Eight.isStrongOffender_natural_iff A

end CFSG.Quasithin.ChapterB.Offenders
