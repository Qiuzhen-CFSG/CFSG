module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalSelectedCoreSylow
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalAction

/-!
# The original selected pair core centralizes the chosen A5 module

The actual pair core lies in T and is normalized by L. Its restriction
to the original five-point action is a solvable normal subgroup of a group
containing A5, hence trivial. Thus it centralizes the whole chosen module.
This does not assert that the right factor normalizes that module.

Source: the original A5 module action, normal two-core action, and 5.2.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H R : Subgroup G}

private theorem two_subgroup_centralizes_chosen
    (d : Context T L V V₁ V₂ V₃) (U : Subgroup G)
    (hU : IsPGroup 2 U) (hUT : U ≤ (T : Subgroup G))
    (hLU : L ≤ normalizer (U : Set G)) : U ≤ centralizer (V : Set G) := by
  let P := L ⊔ U
  have hP : P ≤ L ⊔ (T : Subgroup G) := sup_le_sup_left hUT L
  let f := d.localActor.comp (inclusion hP)
  have hA : alternatingGroup (Fin 5) ≤ f.range := by
    intro a ha
    obtain ⟨l,hl⟩ := d.flag.module.onto ⟨a,ha⟩
    refine ⟨⟨l,(show L ≤ P from le_sup_left) l.property⟩,?_⟩
    change d.flag.normalizerAction ⟨l,_⟩ = a
    exact (d.flag.action_agrees l (d.flag.module.normalizes l.property)).trans
      (congrArg Subtype.val hl)
  let : (U.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le hLU U.le_normalizer)
  let : Group.IsNilpotent (U.subgroupOf P) := hU.comap_subtype.isNilpotent
  have hk := Theory.SpecificGroups.FivePointSylowParabolic.solvable_normal_le_ker
    f hA (U.subgroupOf P)
  intro u hu
  have he : d.flag.normalizerAction ⟨u,d.flag.T_normalizes (hUT hu)⟩ = 1 :=
    hk (show (⟨u,(show U ≤ P from le_sup_right) hu⟩ : P) ∈ U.subgroupOf P from hu)
  exact (Section05.A5Source.actor_eq_one_iff d.flag
    ⟨u,d.flag.T_normalizes (hUT hu)⟩).mp he

/-- The literal selected pair two-core acts trivially on the original
chosen module, under the unchanged source selection clauses. -/
theorem original_selected_pair_core_centralizes_module
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : R ⊔ (T : Subgroup G) = H)
    (hind : ((T : Subgroup G) ⊓ normalizer (R : Set G)).relIndex
      (T : Subgroup G) ≤ 2)
    (hSR : Global.sourceS L H ≤ normalizer (R : Set G)) :
    (ChapterF.Source.generated ![L,R] (Global.sourceS L H)).pCoreIn 2 ≤
      centralizer (V : Set G) := by
  let N := ChapterF.Source.generated ![L,R] (Global.sourceS L H)
  apply two_subgroup_centralizes_chosen d (N.pCoreIn 2) (isPGroup_pCoreIn 2 N)
  · exact (original_selected_pair_core_le_normalizing_sylow d hH hgen hind hSR).trans inf_le_left
  · exact (show L ≤ N from le_sup_left.trans le_sup_left).trans
      (N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
