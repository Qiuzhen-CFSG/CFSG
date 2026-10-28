module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Representatives
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Dimensions
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.ExceptionalBest.FixedDimensions

/-!
# The exceptional degree-eight group is a best offender

The concrete group `A₀` has rank four and fixed dimensions three on the core
and two on the natural module. Its weights are therefore seven and six.
An exhaustive calculation on its 67 word subgroups proves that no subgroup
has larger weight, including the trivial subgroup and the additional fixed
vectors arising in the natural quotient.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(2),(5),(6), printed pp. 83–84. These are the exceptional-family
sufficiency statements; conjugacy transport and the other families are separate.
-/

public section
open BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Offenders.Eight

/-- Every subgroup of `A₀` has core weight at most seven and natural weight
at most six. The comparison includes the trivial subgroup. -/
theorem exceptional_subgroup_weights (B : Subgroup Perm)
    (hB : B ≤ exceptional 8 (by decide)) :
    weight (coreRepresentation (Fin 8)) B ≤ 7 ∧
    weight (naturalRepresentation (Fin 8)) B ≤ 6 :=
  ExceptionalBest.subgroup_weights B hB

/-- The exceptional group is a best offender on the core permutation module. -/
theorem isBestOffender_exceptional_core :
    IsBestOffender (coreRepresentation (Fin 8)) (exceptional 8 (by decide)) := by
  refine ⟨isElementaryTwo_exceptional, ?_⟩
  intro B hB
  have hweight : weight (coreRepresentation (Fin 8)) (exceptional 8 (by decide)) = 7 := by
    rw [weight, rank_exceptional, finrank_fixedSpace_exceptional.2.2.1]
  rw [hweight]
  exact (exceptional_subgroup_weights B hB).1

/-- The exceptional group is a best offender on the natural permutation module. -/
theorem isBestOffender_exceptional_natural :
    IsBestOffender (naturalRepresentation (Fin 8)) (exceptional 8 (by decide)) := by
  refine ⟨isElementaryTwo_exceptional, ?_⟩
  intro B hB
  have hweight : weight (naturalRepresentation (Fin 8)) (exceptional 8 (by decide)) = 6 := by
    rw [weight, rank_exceptional, finrank_fixedSpace_exceptional.2.2.2]
  rw [hweight]
  exact (exceptional_subgroup_weights B hB).2

end CFSG.Quasithin.ChapterB.Offenders.Eight
