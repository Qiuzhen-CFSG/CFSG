module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport

/-!
# Core displacement by a block in a relative overgroup

The ambient two-core acts on a subnormal short group with commutators in
its intrinsic U-layer. Transport this statement from a subgroup H back to
the original ambient group, keeping H's two-core and the literal subtype
maps. No subnormality in the larger group is required.

OriginalCentralization/TwoBlocks uses this separately in LT and KT=H.
Source: Aschbacher--Smith C.1.11, printed p.124, applied to the original
pair in the nonsolvable step of 13.2.8(1), p.880.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]
theorem relative_core_commutator_le_blockU
    {K H : Subgroup G} (hKH : K ≤ H) (hK : IsBlock (K.subgroupOf H)) :
    ⁅H.pCoreIn 2,K⁆ ≤ (blockU K).map K.subtype := by
  let A := K.subgroupOf H
  let e : A ≃* K := subgroupOfEquivOfLe hKH
  have hc : ⁅pCore 2 H,A⁆ ≤ (blockU A).map A.subtype :=
    commutator_le_core_commutator_of_isSubnormal A (pCore 2 H)
      hK.subnormal hK.short.twoPerfect pCore_isPGroup le_normalizer_of_normal
  have hh := map_mono (f := H.subtype) hc
  rw [map_commutator,map_subgroupOf_eq_of_le hKH] at hh
  have he : (blockU A).map (H.subtype.comp A.subtype) =
      (blockU K).map K.subtype := by
    rw [←RankOne.Solvable.blockU_map_equiv e,map_map]
    rfl
  rw [map_map,he] at hh
  exact hh
end CFSG.Quasithin.ChapterC

