module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# A self-centralizing solvable normal subgroup excludes components

A component either lies in a normal subgroup or centralizes it. If the normal
subgroup is solvable and contains its centralizer, either case would place a
nontrivial perfect group inside a solvable group, a contradiction.

This intrinsic action criterion applies to the normal two-kernels of sporadic
involution centralizers in Aschbacher–Smith 16.1.5–7, printed pp.1171–1173.
An extension shape alone does not supply the centralizer containment.
-/

public section
namespace Theory.GroupTheory
open Subgroup

/-- Normality and the actual kernel action, rather than the quotient's order,
exclude every quasisimple component. -/
theorem not_isComponent_of_solvable_normal_selfCentralizing
    {G : Type*} [Group G] [Finite G] (Q : Subgroup G) [Q.Normal]
    [Group.IsSolvable Q] (hc : centralizer (Q : Set G) ≤ Q) (K : Subgroup G) :
    ¬ IsComponent G K := by
  intro hK
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hKQ : K ≤ Q := by
    rcases hK.normal_dichotomy Q with h | h
    · exact h
    · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans hc
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hKQ)
  exact Group.IsPerfect.not_isSolvable K inferInstance

end Theory.GroupTheory
