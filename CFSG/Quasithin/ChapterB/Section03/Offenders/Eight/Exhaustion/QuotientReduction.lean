module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.QuotientReduction.Transitive
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.QuotientReduction.Intransitive

/-!
# Quotient necessity reductions in degree eight

Constant displacements measure the exact difference between the full and
deleted fixed codimensions. The intransitive orbit-kernel bound contradicts
the natural-offender inequality whenever the displacement space is nonzero.
Full-module necessity then settles the deleted case, while restriction to the
natural module leaves defect at most one. A common fixed coordinate gives
case (a) on both quotient sections. The transitive branch gives every clause
of the regular alternative and cannot occur on the deleted module.

Thus deleted best offenders belong to case (a). Natural best offenders belong
to case (a), are regular, or have no common fixed coordinate and full fixed
codimension at most their rank plus one. This last numerical alternative still
requires a separate orbit classification for the full source theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(4),(6), printed pp. 83–84.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders.EightExhaustion

open BinaryPermutation Representation.BinaryOffender
open BinaryPermutation.QuotientFixedSpace

/-- Without additional quotient fixed vectors, deleted offenders are full offenders. -/
theorem caseAFamily_of_isOffender_deleted_of_displacementRank_eq_zero
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (deletedRepresentation (Fin 8)) A)
    (hd : displacementRank A (0 : Fin 8) = 0) : CaseAFamily 8 A := by
  apply caseAFamily_of_isOffender_full
  refine ⟨hA.1, ?_⟩
  have h := fixedCodim_deleted_add_displacementRank A (0 : Fin 8)
  simpa only [hd, Nat.add_zero, h.symm] using hA.2

/-- A common fixed coordinate forces deleted offenders into case (a). -/
theorem caseAFamily_of_isOffender_deleted_of_fixed_point
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (deletedRepresentation (Fin 8)) A)
    {x : Fin 8} (hx : ∀ a ∈ A, a x = x) : CaseAFamily 8 A :=
  caseAFamily_of_isOffender_deleted_of_displacementRank_eq_zero hA
    (displacementRank_eq_zero_of_fixed_point hx 0)

/-- A common fixed coordinate forces natural offenders into case (a). -/
theorem caseAFamily_of_isOffender_natural_of_fixed_point
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (naturalRepresentation (Fin 8)) A)
    {x : Fin 8} (hx : ∀ a ∈ A, a x = x) : CaseAFamily 8 A := by
  apply caseAFamily_of_isOffender_core_of_fixed_point (x := x) _ hx
  refine ⟨hA.1, ?_⟩
  rw [← fixedCodim_natural_eq_core_of_lift (by decide : Even (Fintype.card (Fin 8))) A
    (fixedPreimage_eq_full_of_fixed_point hx)]
  exact hA.2

/-- Natural offenders outside case (a) have no common fixed coordinate. -/
theorem no_fixed_point_of_isOffender_natural_of_not_caseA
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (naturalRepresentation (Fin 8)) A) (hn : ¬ CaseAFamily 8 A) :
    ∀ x : Fin 8, ∃ a ∈ A, a x ≠ x := by
  intro x
  by_contra! hx
  exact hn (caseAFamily_of_isOffender_natural_of_fixed_point hA hx)

/-- Vanishing displacement characters give the required defect-one bound. -/
theorem full_fixedCodim_le_rank_add_one_of_isOffender_natural_of_displacementRank_eq_zero
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (naturalRepresentation (Fin 8)) A)
    (hd : displacementRank A (0 : Fin 8) = 0) :
    fixedCodim (representation (Fin 8)) A ≤ rank A + 1 := by
  have h := fixedCodim_deleted_add_displacementRank A (0 : Fin 8)
  have hb := fixedCodim_deleted_le_natural_add_one
    (by decide : Even (Fintype.card (Fin 8))) A
  have ho := hA.2
  omega

/-- The offender inequality forces a lower bound on rank plus orbit and
displacement dimensions. This is incompatible with the orbit-kernel
upper bound for intransitive actions with nonzero displacement. -/
theorem seven_le_rank_add_displacementRank_add_orbits_of_isOffender_natural
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (naturalRepresentation (Fin 8)) A) :
    7 ≤ rank A + displacementRank A (0 : Fin 8) +
      Nat.card (MulAction.orbitRel.Quotient A (Fin 8)) := by
  have h := fixedCodim_deleted_add_displacementRank A (0 : Fin 8)
  have hb := fixedCodim_deleted_le_natural_add_one
    (by decide : Even (Fintype.card (Fin 8))) A
  have hf := fixedCodim_full_add_card_orbits A
  simp only [Fintype.card_fin] at hf
  have ho := hA.2
  omega

/-- A numerical orbit-kernel estimate forces the displacement space to vanish. -/
theorem displacementRank_eq_zero_of_isOffender_natural_of_orbit_bound
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (naturalRepresentation (Fin 8)) A)
    (hb : 0 < displacementRank A (0 : Fin 8) →
      rank A + displacementRank A (0 : Fin 8) +
        Nat.card (MulAction.orbitRel.Quotient A (Fin 8)) ≤ 6) :
    displacementRank A (0 : Fin 8) = 0 := by
  have h := seven_le_rank_add_displacementRank_add_orbits_of_isOffender_natural hA
  by_contra hn
  have := hb (Nat.pos_of_ne_zero hn)
  omega

/-- Intransitive natural offenders have no additional quotient fixed vectors:
positive displacement would force the rank-orbit sum both above six and below seven. -/
theorem displacementRank_eq_zero_of_isOffender_natural_of_intransitive
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (naturalRepresentation (Fin 8)) A)
    (ht : ¬ (∀ x y : Fin 8, ∃ a : A, a.val x = y)) :
    displacementRank A (0 : Fin 8) = 0 :=
  displacementRank_eq_zero_of_isOffender_natural_of_orbit_bound hA
    (rank_add_displacementRank_add_orbits_le_six_of_intransitive hA.1 ht)

/-- Every deleted-module offender is conjugate to an actual `A_m`, `1 ≤ m ≤ 4`. -/
theorem caseAFamily_of_isOffender_deleted {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (deletedRepresentation (Fin 8)) A) : CaseAFamily 8 A := by
  have hn : IsOffender (naturalRepresentation (Fin 8)) A :=
    ⟨hA.1, (fixedCodim_natural_le_deleted A).trans hA.2⟩
  apply caseAFamily_of_isOffender_deleted_of_displacementRank_eq_zero hA
  exact displacementRank_eq_zero_of_isOffender_natural_of_intransitive hn
    (fun ht => not_isOffender_deleted_of_transitive ht hA)

/-- B.3.2(4), necessity on the deleted module in degree eight. -/
theorem caseAFamily_of_isBestOffender_deleted {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsBestOffender (deletedRepresentation (Fin 8)) A) : CaseAFamily 8 A :=
  caseAFamily_of_isOffender_deleted (hA.isOffender _)

/-- Natural offenders reduce to case (a), the regular case, or an action with
no common fixed coordinate and defect at most one on the full module. -/
theorem caseAFamily_or_isRegularEight_or_defect_one_of_isOffender_natural
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (naturalRepresentation (Fin 8)) A) :
    CaseAFamily 8 A ∨ IsRegularEight A ∨
      ((∀ x : Fin 8, ∃ a ∈ A, a x ≠ x) ∧
        fixedCodim (representation (Fin 8)) A ≤ rank A + 1) := by
  by_cases hc : CaseAFamily 8 A
  · exact Or.inl hc
  by_cases ht : ∀ x y : Fin 8, ∃ a : A, a.val x = y
  · exact Or.inr (Or.inl (isRegularEight_of_transitive hA.1 ht))
  exact Or.inr (Or.inr
    ⟨no_fixed_point_of_isOffender_natural_of_not_caseA hA hc,
      full_fixedCodim_le_rank_add_one_of_isOffender_natural_of_displacementRank_eq_zero hA
        (displacementRank_eq_zero_of_isOffender_natural_of_intransitive hA ht)⟩)

/-- Numerical necessity reduction for B.3.2(6) in degree eight. The last
alternative remains to be classified by the separate orbit-defect argument. -/
theorem caseAFamily_or_isRegularEight_or_defect_one_of_isBestOffender_natural
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsBestOffender (naturalRepresentation (Fin 8)) A) :
    CaseAFamily 8 A ∨ IsRegularEight A ∨
      ((∀ x : Fin 8, ∃ a ∈ A, a x ≠ x) ∧
        fixedCodim (representation (Fin 8)) A ≤ rank A + 1) :=
  caseAFamily_or_isRegularEight_or_defect_one_of_isOffender_natural (hA.isOffender _)

end CFSG.Quasithin.ChapterB.Offenders.EightExhaustion
