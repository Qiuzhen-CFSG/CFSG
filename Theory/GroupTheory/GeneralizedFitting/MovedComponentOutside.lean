module
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer

/-!
# A moved component outside an overgroup containing the actor in its core

With trivial two-core, a nontrivial two-subgroup centralizing the odd core
must move a component, by the generalized-Fitting centralizer theorem.
If the actor lies in the two-core of an overgroup, that component cannot
lie in the overgroup: components centralize solvable normal subgroups.

Source: Aschbacher--Smith, the opening component selection following
Lemma4.4.9 and Lemma4.4.10(1), printed p.621.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G:Type*} [Group G] [Finite G]

/-- Select an actual ordinary component outside the specified overgroup. -/
theorem exists_component_moved_outside_of_centralizes_oddCore
    (V H:Subgroup G) (hV:IsPGroup 2 V) (hne:V≠⊥)
    (hcore:pCore 2 G=⊥) (hodd:⁅V,pPrimeCore 2 G⁆=⊥)
    (hVH:V≤H.pCoreIn 2) :
    ∃K:Subgroup G,IsComponent G K ∧ ⁅K,V⁆≠⊥ ∧ ¬K≤H := by
  have hVF:V≤centralizer (fittingSubgroup G:Set G):=
    (commutator_eq_bot_iff_le_centralizer.mp hodd).trans
      (centralizer_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore))
  obtain ⟨K,hK,hm⟩:=exists_component_moved_of_centralizes_fitting 2 V hV hne hcore hVF
  refine ⟨K,hK,hm,?_⟩
  intro hKH
  let : Group.IsNilpotent (pCore 2 H):=pCore_isNilpotent
  have hc:K.subgroupOf H≤centralizer (pCore 2 H:Set H):=
    (hK.subgroupOf hKH).le_centralizer_of_solvable_normal (pCore 2 H)
  apply hm
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro k hk v hv
  obtain ⟨w,hw,rfl⟩:=hVH hv
  exact congrArg Subtype.val (hc (show (⟨k,hKH hk⟩:H)∈K.subgroupOf H from hk) w hw)
end Theory.GroupTheory
