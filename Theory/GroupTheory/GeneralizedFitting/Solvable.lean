module

public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# The generalized Fitting subgroup of a solvable group

A solvable group has no nontrivial perfect subgroup, hence has no components.
Its generalized Fitting subgroup is therefore its ordinary Fitting subgroup.
The source application is the solvable binary action in D.2.19 and Section 15.1.
-/

public section
namespace Theory.GroupTheory
open Subgroup

variable (G : Type*) [Group G] [Group.IsSolvable G]

theorem componentLayer_eq_bot_of_solvable : componentLayer G = ⊥ := by
  apply sSup_eq_bot.mpr
  intro K hK
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact (Group.IsPerfect.not_isSolvable K inferInstance).elim

theorem generalizedFitting_eq_fitting_of_solvable :
    generalizedFitting G = fittingSubgroup G := by
  rw [generalizedFitting, componentLayer_eq_bot_of_solvable G, sup_bot_eq]

end Theory.GroupTheory
