module
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.CoreGrowth
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Original 14.1.17(1) in the orthogonal Chapter 15 case

The literal natural action has reduced quotient and central seed of order two.
Its kernel lies in Mc. If the intersection core centralized the module, normal
core intersection would identify it with O₂(M). The source core-growth theorem
for the same two distinct maximal locals excludes that equality. Thus the
original intersection core acts nontrivially, with no core-growth, block, or
noncentrality premise retained.

Source: Aschbacher–Smith 14.1.14, 14.1.17(1), and 15.3.7, pp.979–980,1122.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03
open ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

theorem intersection_core_noncentral_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : Mc ≠ M) :
    ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (localModule T M : Set G) := by
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    apply hMcC.2
    intro z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hC : M ⊓ centralizer (localModule T M : Set G) ≤ Mc :=
    inf_le_right.trans ((centralizer_le (le_conjugateSpanBy _ _)).trans hMcC.2)
  have hQK : pCore 2 M ≤ d.actor.ker := by
    have hn : ((pCore 2 M).map d.actor).Normal :=
      (inferInstance : (pCore 2 M).Normal).map _ d.onto
    have hp : (pCore 2 M).map d.actor ≤ pCore 2 OrthogonalActor :=
      le_sSup ⟨hn,pCore_isPGroup.map _⟩
    apply (Subgroup.map_eq_bot_iff _).mp
    have hactor : pCore 2 OrthogonalActor = ⊥ := WreathTwoResidual.twoCore_eq_bot
    exact le_bot_iff.mp (hactor ▸ hp)
  let C := d.actor.ker
  have hCI : C.map M.subtype ≤ M ⊓ Mc := by
    rw [show C = d.actor.ker from rfl,d.ker_actor,subgroupOf_map_subtype,inf_comm]
    exact le_inf inf_le_left hC
  have hCcore : C.pCoreIn 2 = pCore 2 M := by
    rw [pCoreIn,pCore_eq_comap_of_normal,map_comap_eq,range_subtype,inf_eq_right.mpr hQK]
  intro hcentral
  have hRC : (M ⊓ Mc).pCoreIn 2 ≤ C.map M.subtype := by
    rw [show C = d.actor.ker from rfl,d.ker_actor,subgroupOf_map_subtype]
    exact le_inf hcentral ((pCoreIn_le 2 (M ⊓ Mc)).trans inf_le_left)
  have he : (M ⊓ Mc).pCoreIn 2 = M.pCoreIn 2 := by
    apply le_antisymm
    · have hi := inf_pCoreIn_le_of_le 2 hCI
      rw [←map_pCoreIn_of_injective 2 C M.subtype M.subtype_injective,hCcore] at hi
      exact (le_inf hRC le_rfl).trans hi
    · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M)
        ((map_mono hQK).trans hCI)
        (inf_le_left.trans (M.le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))
  exact Chapter14.SourcePreliminaries.intersection_core_ne_local_core
    hG T hempty hM.1 ⟨hMcC.1,hTMc⟩ hu hmany
    (d.card_centralInvolutions T hM.1.2) (Ne.symm hne) he

end CFSG.Quasithin.Chapter15.Section03
