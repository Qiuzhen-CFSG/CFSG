module
public import CFSG.Quasithin.Chapter10.SourceBaumannBlocks

/-!
# Placement of the original alternating-five block layer

The block selected by E.2.3 has its intrinsic layer inside the actual local
module. Every generating component of the local join is a Sylow conjugate
of the original component. Functoriality of the intrinsic block layer and
normality of the local module therefore place the original block layer in
that module as well. This keeps the original group and module, and does not
assume that the full module equals the local module.

Source: Aschbacher–Smith, 10.2.1 and E.2.3, printed pp.742–743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

theorem source_original_block_module_le_of_generating_component
    (K : Subgroup (localJoin T L)) (hK : K.IsCComponent)
    (hgen : K ⊔ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) = ⊤)
    (hUK : (blockU K).map K.subtype ≤ D.moduleSubgroup.subgroupOf (localJoin T L)) :
    (blockU L).map L.subtype ≤ D.moduleSubgroup := by
  let H := localJoin T L
  let A := L.subgroupOf H
  let U := D.moduleSubgroup.subgroupOf H
  let : U.Normal := (source_parabolic_module_reduced D).normal
  obtain ⟨s,hs⟩ := source_original_component_conjugate_of_generating_component D K hK hgen
  let c := MulAut.conj (s : H)
  let a := (c.subgroupMap K).trans (MulEquiv.subgroupCongr hs.symm)
  have he : ((blockU K).map K.subtype).map c.toMonoidHom = (blockU A).map A.subtype := by
    rw [←RankOne.Solvable.blockU_map_equiv a,map_map,map_map]
    rfl
  have hAU : (blockU A).map A.subtype ≤ U := by
    rw [←he]
    exact (map_mono hUK).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp ((show (⊤ : Subgroup H) ≤ normalizer (U : Set H) from
        le_normalizer_of_normal) (mem_top (s : H))))
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  let b : A ≃* L := subgroupOfEquivOfLe hLH
  have hb : (blockU L).map L.subtype = ((blockU A).map A.subtype).map H.subtype := by
    rw [←RankOne.Solvable.blockU_map_equiv b,map_map,map_map]
    rfl
  rw [hb]
  exact (map_mono hAU).trans_eq (map_subgroupOf_eq_of_le
    (D.module_le_sylow.trans (show (T : Subgroup G) ≤ H from le_sup_right)))

theorem source_a5_original_block_module_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    (blockU L).map L.subtype ≤ D.moduleSubgroup := by
  have hfive := (source_a5_baumann_normalizer_or_five_action_unconditional D e hn).resolve_left hout
  obtain ⟨K,hK,_,_,hgen,hUK⟩ := source_five_action_generating_block_with_module D
    (source_a5_minimal_parabolic D e hn) hfive hout
  exact source_original_block_module_le_of_generating_component D K hK hgen hUK
end CFSG.Quasithin.Chapter10
