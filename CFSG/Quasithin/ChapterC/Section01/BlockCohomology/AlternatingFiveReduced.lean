module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.ReducedClosure
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
/-!
# The reduced module and direct core split of a normal A₅ block

The A₅ layer is reduced by the existing Sylow-fixed normal-closure theorem.
Thus its commutator with the block lies in the ambient reduced subgroup,
while the ambient-core commutator bound gives the reverse inclusion.
Transport to a normalizing overgroup identifies its literal reduced moved
module with the intrinsic layer. The C.1.13(c) split and the layer's zero
fixed points then give the required direct core decomposition.

Source: Aschbacher--Smith C.1.13(c), p.125, and the final paragraph of
13.3.14, p.893. The block recognition and chief-count estimate precede this
calculation and are not asserted here.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]
/-- A normal A₅ block has precisely its own layer as reduced commutator. -/
theorem IsAlternatingBlock.normal_reduced_commutator (K : Subgroup G) [K.Normal]
    (hK : IsAlternatingBlock K 5) :
    ⁅reducedTwoSubgroup G,K⁆ = (blockU K).map K.subtype := by
  let U := (blockU K).map K.subtype
  have hU : U ≤ pCore 2 G :=
    le_sSup ⟨inferInstance, (pCore_isPGroup.to_le blockU_le_core).map K.subtype⟩
  have hr := hK.normalClosure_layer_reduced K (default : Sylow 2 G)
    le_normalizer_of_normal hU
  have he : normalClosure (U : Set G) = U := normalClosure_eq_self U
  change IsPReduced 2 (normalClosure (U : Set G)) at hr
  rw [he] at hr
  have hblock : IsBlock K := ⟨inferInstance,hK.2.1,Normal.isSubnormal inferInstance⟩
  apply le_antisymm
  · exact (commutator_mono (reducedPSubgroup_le_pCore 2 G) le_rfl).trans_eq
      hblock.ambient_core_commutator
  · have hm := congrArg (map K.subtype) (ExceptionalRestrictions.short_commutator hK.2.1)
    rw [map_commutator, ←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm.symm.le.trans (commutator_mono hr.le_reducedPSubgroup le_rfl)

/-- The same identity in any normalizing overgroup, on the original ambient maps. -/
theorem IsAlternatingBlock.normalizer_reduced_commutator (K H : Subgroup G)
    (hK : IsAlternatingBlock K 5) (hKH : K ≤ H)
    (hn : H ≤ normalizer (K : Set G)) :
    ⁅(reducedTwoSubgroup H).map H.subtype,K⁆ = (blockU K).map K.subtype := by
  let K₀ := K.subgroupOf H
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer hn
  let e : K₀ ≃* K := subgroupOfEquivOfLe hKH
  have hK₀ := RankOne.Solvable.isAlternatingBlock_of_equiv e.symm hK
  have hm := congrArg (map H.subtype) (hK₀.normal_reduced_commutator K₀)
  rw [map_commutator,map_subgroupOf_eq_of_le hKH] at hm
  have he : ((blockU K₀).map K₀.subtype).map H.subtype = (blockU K).map K.subtype := by
    rw [map_map]
    have hh : H.subtype.comp K₀.subtype = K.subtype.comp e.toMonoidHom := rfl
    rw [hh,←map_map,RankOne.Solvable.blockU_map_equiv e]
  exact hm.trans he
omit [Finite G] in
omit [Finite G] in
/-- The intrinsic A₅ layer meets the ambient block centralizer trivially. -/
theorem IsAlternatingBlock.layer_inf_centralizer_eq_bot (K : Subgroup G)
    (hK : IsAlternatingBlock K 5) :
    (blockU K).map K.subtype ⊓ centralizer (K : Set G) = ⊥ := by
  apply bot_unique
  rintro x ⟨⟨k,hk,rfl⟩,hc⟩
  have hz : k ∈ center K := by
    apply mem_center_iff.mpr
    intro z
    exact Subtype.ext (hc z z.property)
  have he : blockU K ⊓ center K = ⊥ := by
    rw [←blockFixed_map,hK.blockFixed_eq_bot,Subgroup.map_bot]
  exact congrArg K.subtype (mem_bot.mp (he ▸ (show k ∈ blockU K ⊓ center K from ⟨hk,hz⟩)))

/-- The core of the normalizer splits directly over the original reduced
moved module, with no separate layer-identification hypothesis. -/
theorem IsAlternatingBlock.normalizer_core_reduced_decomposition (K H : Subgroup G)
    (hK : IsAlternatingBlock K 5) (hKH : K ≤ H)
    (hn : H ≤ normalizer (K : Set G)) :
    (H.pCoreIn 2 ⊓ centralizer (K : Set G)) ⊔
        ⁅(reducedTwoSubgroup H).map H.subtype,K⁆ = H.pCoreIn 2 ∧
      Disjoint (H.pCoreIn 2 ⊓ centralizer (K : Set G))
        ⁅(reducedTwoSubgroup H).map H.subtype,K⁆ := by
  rw [hK.normalizer_reduced_commutator K H hKH hn]
  refine ⟨?_,?_⟩
  · exact (sup_comm _ _).trans (hK.normalizer_twoCore_eq_module_sup_centralizer hKH hn).symm
  · exact (disjoint_iff.mpr (hK.layer_inf_centralizer_eq_bot K)).symm.mono_left inf_le_right

end CFSG.Quasithin.ChapterC
