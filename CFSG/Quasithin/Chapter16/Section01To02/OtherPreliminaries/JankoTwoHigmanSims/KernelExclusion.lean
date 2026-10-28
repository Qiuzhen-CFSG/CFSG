module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Excluding components using the centralizer kernel action

A component either lies in or centralizes a normal two-subgroup. If that
two-subgroup contains its centralizer, either case places the component inside
a two-group, contradicting perfectness and nontriviality. The normality here
is inside the group whose components are being tested.

This is the action-dependent exclusion needed for the extension cases in
Aschbacher–Smith 16.1.5(8),(10) and their use in 16.1.7, printed pp.1172–1173.
The concrete normal kernels and their centralizers remain model obligations.
-/

public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims

open Subgroup Theory.GroupTheory

/-- A proved self-centralizing normal two-kernel rules out every component. -/
theorem HasSelfCentralizingNormalTwoSubgroup.not_isComponent
    {C : Type*} [Group C] [Finite C]
    (h : HasSelfCentralizingNormalTwoSubgroup C) (K : Subgroup C) :
    ¬ IsComponent C K := by
  obtain ⟨Q, hQn, hQ, hself⟩ := h
  let := hQn
  intro hK
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hKQ : K ≤ Q := by
    rcases hK.normal_dichotomy Q with hle | hc
    · exact hle
    · exact (commutator_eq_bot_iff_le_centralizer.mp hc).trans hself
  let : Group.IsNilpotent K := (hQ.to_le hKQ).isNilpotent
  exact Group.IsPerfect.not_isSolvable K inferInstance

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
