module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Ambient.Source
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
/-!
# The literal local-to-ambient cubic block consumer

For `K ≤ H ≤ G`, transport the actual local block, original Thompson movement
and block-module support through subgroup inclusion. The same ambient image
of `K` is an alternating-three block, and its full block module is precisely
the nonzero commutator with the ambient omega-center span.

This is the solvable-action ambient lift used after the fixed characteristic
pair produces a local cubic block. Neither a new block witness nor a control
subgroup is supplied as an assumption.
Source: Aschbacher--Smith C.1.27--28, printed pp.132--134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Ambient
variable {G : Type*} [Group G] [Finite G]

theorem local_alternatingThree_maps_to_ambient
    (T : Sylow 2 G) (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (K : Subgroup H) (hK : IsBlock K) (ha : IsAlternatingBlock K 3)
    (hJ : K = ⁅K,elementaryAbelianMaxJ (T.subtype hTH : Subgroup H)⁆)
    (hU : ((blockU K).map K.subtype).map H.subtype ≤
      normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hsolv : Group.IsSolvable (G ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))) :
    let A := K.map H.subtype
    let V := normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)
    IsBlock A ∧ IsAlternatingBlock A 3 ∧
      A = ⁅A,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU A).map A.subtype = ⁅V,A⁆ ∧ ⁅V,A⁆ ≠ ⊥ := by
  let A := K.map H.subtype
  let V := normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)
  let e : K ≃* A := K.equivMapOfInjective H.subtype H.subtype_injective
  have haA : IsAlternatingBlock A 3 := Solvable.isAlternatingBlock_of_equiv e ha
  have hAH : A ≤ H := map_subtype_le K
  have hs : (A.subgroupOf H).IsSubnormal := by
    simpa only [A,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hK.subnormal
  have hm : A = ⁅A,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
    have hh := congrArg (Subgroup.map H.subtype) hJ
    rwa [map_commutator,←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hh
  have hu : (blockU A).map A.subtype ≤ V := by
    rw [←Solvable.blockU_map_equiv e,map_map]
    have hh := hU
    rw [map_map] at hh
    exact hh
  obtain ⟨hb,hn⟩ := same_block_of_solvable_omega_action T hchar H A hTH hAH hs haA hm hu hsolv
  have hv : IsPReduced 2 V := omegaCenter_normalClosure_reduced T hchar
  let : IsElementaryAbelian 2 V := hv.elementary
  exact ⟨hb,haA,hm,SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator A V hb hn,hn⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Ambient
