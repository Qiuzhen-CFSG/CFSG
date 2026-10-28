module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Coordinates
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Dimensions
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Conjugacy
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.DBounds.FixedDimensions

/-!
# All-subgroup bounds inside the degree-eight disjoint-swap group

Every subgroup of `D₈ ≃ C₂⁴` has binary rank at most its deleted fixed
codimension. Every proper subgroup has the same bound on the core and natural
modules. This includes the trivial subgroup and the full-support cyclic group,
whose quotient has extra fixed vectors of nonzero constant displacement.

The proof transports the complete binary subgroup table to sixteen classes
under pair permutations, then uses exact fixed-vector counts. The bounds compare
every proper subgroup of each `A_m` with the ambient module dimension, proving
that all four representatives are best offenders on all three sections.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(1),(4)–(6), printed pp. 83–84.
-/

public section
namespace CFSG.Quasithin.ChapterB.Offenders.Eight
open Representation.BinaryOffender BinaryPermutation
namespace DBounds
private theorem representative_deleted_bound (j : Fin 16) :
    rank (group (representative j)) ≤
      fixedCodim (deletedRepresentation (Fin 8)) (group (representative j)) := by
  have hc := codimensions _ _ _ _ _ (dimensions_representative j)
  rw [rank_representative, hc.2.1]
  clear hc
  revert j
  decide +kernel

private theorem representative_core_natural_bound (j : Fin 16) (hj : j ≠ 15) :
    rank (group (representative j)) ≤
      fixedCodim (coreRepresentation (Fin 8)) (group (representative j)) ∧
    rank (group (representative j)) ≤
      fixedCodim (naturalRepresentation (Fin 8)) (group (representative j)) := by
  have hc := codimensions _ _ _ _ _ (dimensions_representative j)
  rw [rank_representative, hc.2.2.1, hc.2.2.2]
  clear hc
  revert j
  decide +kernel

private theorem group_last : group 66 = D 8 := by
  ext g
  rw [mem_group, mem_D_iff]
  have hm : members 66 = Finset.univ := by decide +kernel
  simp only [hm, Finset.mem_univ, true_and]

private theorem proper_index {i : Fin 67} (hi : group i < D 8) :
    representativeIndex i ≠ 15 := by
  intro he
  have hh : ∀ i : Fin 67, representativeIndex i = 15 → i = 66 := by decide +kernel
  have := hh i he
  subst i
  rw [group_last] at hi
  exact lt_irrefl _ hi

end DBounds
open DBounds

/-- Every subgroup of `D`, including the trivial one, satisfies the deleted bound. -/
theorem rank_le_fixedCodim_deleted_of_le_D {B : Subgroup Perm} (hB : B ≤ D 8) :
    rank B ≤ fixedCodim (deletedRepresentation (Fin 8)) B := by
  obtain ⟨i, rfl⟩ := group_exhaustive B hB
  rw [(group_conjugate i).rank_eq,
    (group_conjugate i).fixedCodim_eq (deletedRepresentation (Fin 8))]
  exact representative_deleted_bound _

/-- The core bound holds for every proper subgroup of `D`, including zero. -/
theorem rank_le_fixedCodim_core_of_lt_D {B : Subgroup Perm} (hB : B < D 8) :
    rank B ≤ fixedCodim (coreRepresentation (Fin 8)) B := by
  obtain ⟨i, rfl⟩ := group_exhaustive B hB.le
  rw [(group_conjugate i).rank_eq,
    (group_conjugate i).fixedCodim_eq (coreRepresentation (Fin 8))]
  exact (representative_core_natural_bound _ (proper_index hB)).1

/-- The natural bound retains quotient fixed vectors of constant displacement. -/
theorem rank_le_fixedCodim_natural_of_lt_D {B : Subgroup Perm} (hB : B < D 8) :
    rank B ≤ fixedCodim (naturalRepresentation (Fin 8)) B := by
  obtain ⟨i, rfl⟩ := group_exhaustive B hB.le
  rw [(group_conjugate i).rank_eq,
    (group_conjugate i).fixedCodim_eq (naturalRepresentation (Fin 8))]
  exact (representative_core_natural_bound _ (proper_index hB)).2

private theorem best_of_proper_bounds {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Perm V)
    {A : Subgroup Perm} (hA : IsElementaryTwo A) (hcodim : fixedCodim ρ A ≤ rank A)
    (hproper : ∀ B < A, rank B ≤ fixedCodim ρ B) : IsBestOffender ρ A := by
  refine ⟨hA, ?_⟩
  intro B hB
  rcases hB.eq_or_lt with rfl | hB
  · exact le_rfl
  · have h := hproper B hB
    have hdimA := fixedCodim_add_finrank ρ A
    have hdimB := fixedCodim_add_finrank ρ B
    unfold weight
    omega

private theorem initial_codimensions (m : Fin 5) (hm : 0 < m.val) :
    fixedCodim (deletedRepresentation (Fin 8)) (disjointTranspositions 8 m.val) = m.val ∧
    fixedCodim (coreRepresentation (Fin 8)) (disjointTranspositions 8 m.val) ≤ m.val ∧
    fixedCodim (naturalRepresentation (Fin 8)) (disjointTranspositions 8 m.val) ≤ m.val := by
  fin_cases m
  · norm_num at hm
  · exact ⟨fixedCodim_A1.2.1, fixedCodim_A1.2.2.1.le, fixedCodim_A1.2.2.2.le⟩
  · exact ⟨fixedCodim_A2.2.1, fixedCodim_A2.2.2.1.le, fixedCodim_A2.2.2.2.le⟩
  · exact ⟨fixedCodim_A3.2.1, fixedCodim_A3.2.2.1.le, fixedCodim_A3.2.2.2.le⟩
  · exact ⟨fixedCodim_D.2.1, fixedCodim_D.2.2.1.le.trans (by decide),
      fixedCodim_D.2.2.2.le.trans (by decide)⟩

/-- Each `A_m`, for `1 ≤ m ≤ 4`, is a best offender on the deleted module. -/
theorem isBestOffender_deleted_disjointTranspositions (m : Fin 5) (hm : 0 < m.val) :
    IsBestOffender (deletedRepresentation (Fin 8)) (disjointTranspositions 8 m.val) := by
  apply best_of_proper_bounds _ (isElementaryTwo_disjointTranspositions m hm)
  · rw [(initial_codimensions m hm).1, rank_disjointTranspositions]
  · intro B hB
    exact rank_le_fixedCodim_deleted_of_le_D
      (hB.le.trans (disjointTranspositions_le_D _ _))

/-- Each `A_m`, for `1 ≤ m ≤ 4`, is a best offender on the core module. -/
theorem isBestOffender_core_disjointTranspositions (m : Fin 5) (hm : 0 < m.val) :
    IsBestOffender (coreRepresentation (Fin 8)) (disjointTranspositions 8 m.val) := by
  apply best_of_proper_bounds _ (isElementaryTwo_disjointTranspositions m hm)
  · rw [rank_disjointTranspositions]
    exact (initial_codimensions m hm).2.1
  · intro B hB
    exact rank_le_fixedCodim_core_of_lt_D
      (lt_of_lt_of_le hB (disjointTranspositions_le_D _ _))

/-- Each `A_m`, for `1 ≤ m ≤ 4`, is a best offender on the natural module. -/
theorem isBestOffender_natural_disjointTranspositions (m : Fin 5) (hm : 0 < m.val) :
    IsBestOffender (naturalRepresentation (Fin 8)) (disjointTranspositions 8 m.val) := by
  apply best_of_proper_bounds _ (isElementaryTwo_disjointTranspositions m hm)
  · rw [rank_disjointTranspositions]
    exact (initial_codimensions m hm).2.2
  · intro B hB
    exact rank_le_fixedCodim_natural_of_lt_D
      (lt_of_lt_of_le hB (disjointTranspositions_le_D _ _))

/-- In particular, the unique strong canonical group is best on the core. -/
theorem isBestOffender_core_D : IsBestOffender (coreRepresentation (Fin 8)) (D 8) :=
  isBestOffender_core_disjointTranspositions 4 (by decide)

/-- In particular, the unique strong canonical group is best on the natural module. -/
theorem isBestOffender_natural_D : IsBestOffender (naturalRepresentation (Fin 8)) (D 8) :=
  isBestOffender_natural_disjointTranspositions 4 (by decide)

end CFSG.Quasithin.ChapterB.Offenders.Eight
