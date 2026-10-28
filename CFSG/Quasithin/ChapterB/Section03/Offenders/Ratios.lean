module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Complete
public import Theory.Representation.BinaryOffender.RatioFromStrong

/-!
# Quadratic action ratios of the binary permutation sections

Case (a) has offenders and no strong offenders, hence ratio one. In case (b),
the strong offenders are precisely the conjugates of `D`, of rank `n/2` and
fixed codimension `n/2 - 1`. Thompson replacement gives a quadratic strong
offender, so these ratios are attained in the definition of `q`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(4)–(6), printed pp. 83–84.
-/

public section
namespace CFSG.Quasithin.ChapterB.Offenders
open BinaryPermutation Representation.BinaryOffender
open scoped ENNReal

namespace Odd

theorem quadraticRatios {n : ℕ} (hn : n = 5 ∨ n = 7) :
    quadraticRatio (representation (Fin n)) = 1 ∧
    quadraticRatio (deletedRepresentation (Fin n)) = 1 ∧
    quadraticRatio (coreRepresentation (Fin n)) = 1 ∧
    quadraticRatio (naturalRepresentation (Fin n)) = 1 := by
  have hm : 1 ≤ n / 2 := by rcases hn with rfl | rfl <;> decide
  have h := isOffender_disjointTranspositions hn (m := 1) (by decide) hm
  exact ⟨quadraticRatio_eq_one_of_no_strong _ ⟨_, h.1⟩ (not_isStrongOffender_full hn),
    quadraticRatio_eq_one_of_no_strong _ ⟨_, h.2.2.1⟩ (not_isStrongOffender_deleted hn),
    quadraticRatio_eq_one_of_no_strong _ ⟨_, h.2.1⟩ (not_isStrongOffender_core hn),
    quadraticRatio_eq_one_of_no_strong _ ⟨_, h.2.2.2⟩ (not_isStrongOffender_natural hn)⟩

end Odd

namespace Six

theorem actionRatios_D :
    actionRatio (representation (Fin 6)) (D 6) = 1 ∧
    actionRatio (deletedRepresentation (Fin 6)) (D 6) = 1 ∧
    actionRatio (coreRepresentation (Fin 6)) (D 6) = 2 / 3 ∧
    actionRatio (naturalRepresentation (Fin 6)) (D 6) = 2 / 3 := by
  simp only [actionRatio, rank_D, fixedCodim_D.1, fixedCodim_D.2.1,
    fixedCodim_D.2.2.1, fixedCodim_D.2.2.2]
  norm_num [ENNReal.div_self]

theorem quadraticRatio_full : quadraticRatio (representation (Fin 6)) = 1 :=
  quadraticRatio_eq_one_of_no_strong _
    ⟨D 6, (isOffender_full_iff _).mpr
      (caseAFamily_disjointTranspositions (by decide) (by decide))⟩
    not_isStrongOffender_full

theorem quadraticRatio_deleted : quadraticRatio (deletedRepresentation (Fin 6)) = 1 :=
  quadraticRatio_eq_one_of_no_strong _
    ⟨D 6, (isOffender_deleted_iff _).mpr
      (caseAFamily_disjointTranspositions (by decide) (by decide))⟩
    not_isStrongOffender_deleted

theorem quadraticRatio_core : quadraticRatio (coreRepresentation (Fin 6)) = 2 / 3 := by
  apply quadraticRatio_eq_of_strong_ratios _
    ⟨D 6, (isStrongOffender_core_iff _).mpr (IsConjugateTo.refl _)⟩
  intro A hA
  have hc := (isStrongOffender_core_iff A).mp hA
  simpa only [actionRatio, hc.fixedCodim_eq, hc.rank_eq] using actionRatios_D.2.2.1

theorem quadraticRatio_natural : quadraticRatio (naturalRepresentation (Fin 6)) = 2 / 3 := by
  apply quadraticRatio_eq_of_strong_ratios _
    ⟨D 6, (isStrongOffender_natural_iff _).mpr (IsConjugateTo.refl _)⟩
  intro A hA
  have hc := (isStrongOffender_natural_iff A).mp hA
  simpa only [actionRatio, hc.fixedCodim_eq, hc.rank_eq] using actionRatios_D.2.2.2

end Six

namespace Eight

theorem actionRatios_D :
    actionRatio (representation (Fin 8)) (D 8) = 1 ∧
    actionRatio (deletedRepresentation (Fin 8)) (D 8) = 1 ∧
    actionRatio (coreRepresentation (Fin 8)) (D 8) = 3 / 4 ∧
    actionRatio (naturalRepresentation (Fin 8)) (D 8) = 3 / 4 := by
  simp only [actionRatio, rank_D, fixedCodim_D.1, fixedCodim_D.2.1,
    fixedCodim_D.2.2.1, fixedCodim_D.2.2.2]
  norm_num [ENNReal.div_self]

theorem not_isStrongOffender_full (A : Subgroup Perm) :
    ¬ IsStrongOffender (representation (Fin 8)) A :=
  fun hA => (Nat.not_lt_of_ge (rank_le_fixedCodim_full hA.1)) hA.2

theorem not_isStrongOffender_deleted (A : Subgroup Perm) :
    ¬ IsStrongOffender (deletedRepresentation (Fin 8)) A := by
  intro hA
  have hc := caseAFamily_rank_codim
    (EightExhaustion.caseAFamily_of_isOffender_deleted ⟨hA.1, hA.2.le⟩)
  exact (Nat.ne_of_lt hA.2) hc.2.2

theorem quadraticRatio_full : quadraticRatio (representation (Fin 8)) = 1 :=
  quadraticRatio_eq_one_of_no_strong _
    ⟨D 8, (isBestOffender_full_of_caseAFamily
      (caseAFamily_disjointTranspositions (by decide) (by decide))).isOffender _⟩
    not_isStrongOffender_full

theorem quadraticRatio_deleted : quadraticRatio (deletedRepresentation (Fin 8)) = 1 :=
  quadraticRatio_eq_one_of_no_strong _
    ⟨D 8, isOffender_deleted_of_caseAFamily
      (caseAFamily_disjointTranspositions (by decide) (by decide))⟩
    not_isStrongOffender_deleted

theorem quadraticRatio_core : quadraticRatio (coreRepresentation (Fin 8)) = 3 / 4 := by
  apply quadraticRatio_eq_of_strong_ratios _ ⟨D 8, isStrongOffender_core_D⟩
  intro A hA
  have hc := (isStrongOffender_core_iff A).mp hA
  simpa only [actionRatio, hc.fixedCodim_eq, hc.rank_eq] using actionRatios_D.2.2.1

theorem quadraticRatio_natural : quadraticRatio (naturalRepresentation (Fin 8)) = 3 / 4 := by
  apply quadraticRatio_eq_of_strong_ratios _ ⟨D 8, isStrongOffender_natural_D⟩
  intro A hA
  have hc := (isStrongOffender_natural_iff A).mp hA
  simpa only [actionRatio, hc.fixedCodim_eq, hc.rank_eq] using actionRatios_D.2.2.2

end Eight
end CFSG.Quasithin.ChapterB.Offenders
