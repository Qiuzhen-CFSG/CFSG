module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.CoreIdentification
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NaturalLayerOriginal
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Realization

/-!
# Pulling back the actual symplectic core equality

The source commutator core transports through the specified characteristic
replacement and its holomorph embedding. Once either critical-distance branch
identifies this core with the already recognized natural moving layer, both
inclusions recover the original component core as the original module.
`CoreIdentification` then supplies its elementary, central and irreducible
properties and the intrinsic alternating block conclusion.

Source: MS93 Sections 3 and 5, and Aschbacher--Smith C.1.37, pp.141--143.
The core equality remains the exact conclusion of the distance branches.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T) (h : IntrinsicMSPair d)
include d h
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

omit h [Finite K] in
private theorem original_core_inclusion :
    ((blockU (L.subgroupOf J)).map (L.subgroupOf J).subtype).map (L ⊔ d.B).subtype =
      (blockU L).map L.subtype := by
  let e := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  have he : (blockU (L.subgroupOf J)).map e.toMonoidHom = blockU L := by
    rw [blockU,map_commutator,pCore_map_iso,←MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  rw [map_map]
  change (blockU (L.subgroupOf J)).map (L.subtype.comp e.toMonoidHom) = _
  rw [←map_map,he]

/-- The original core equality pulls back to the original specified module. -/
theorem SourceData.core_image_eq_of_original_core_eq_U
    (he : core R (alpha R) = U R (alpha R)) :
    (blockU L).map L.subtype = V := by
  have hvJ : V ≤ J := (SourceData.module_le_component d).trans le_sup_left
  have hx : (blockU (L.subgroupOf J)).map (L.subgroupOf J).subtype = V.subgroupOf J := by
    rw [← (SourceData.originalSource d h).original_core_pullback,he,
      (SourceData.original_natural_layer d h).2,
      comap_map_eq_self_of_injective (embedM_injective R)]
  rw [← original_core_inclusion d, hx,map_subgroupOf_eq_of_le hvJ]

/-- The characteristic replacement core equality identifies the entire
original intrinsic component core through both specified inclusions. -/
theorem SourceData.core_image_eq_of_reduced_core_eq_U
    (c : CharacteristicReduction (L.subgroupOf J) R)
    (he : core c.radical (alpha c.radical) = U c.radical (alpha c.radical)) :
    (blockU L).map L.subtype = V := by
  have hvJ : V ≤ J := (SourceData.module_le_component d).trans le_sup_left
  have hvH : V.subgroupOf J ≤ c.overgroup :=
    (SourceData.originalSource d h).module_le_component.trans le_sup_left
  have hx : (blockU (L.subgroupOf J)).map (L.subgroupOf J).subtype = V.subgroupOf J := by
    change (⁅pCore 2 (L.subgroupOf J),(⊤ : Subgroup (L.subgroupOf J))⁆).map
      (L.subgroupOf J).subtype = V.subgroupOf J
    rw [← (SourceData.originalSource d h).reduced_core_pullback_internal c,he,
      (SourceData.reduced_natural_layer d h c).2,
      comap_map_eq_self_of_injective (embedM_injective c.radical),
      map_subgroupOf_eq_of_le hvH]
  rw [← original_core_inclusion d, hx,map_subgroupOf_eq_of_le hvJ]

/-- The exact eventual consumer of both critical-distance branches. -/
theorem SourceData.coreReconstruction_of_reduced_core_eq_U
    (c : CharacteristicReduction (L.subgroupOf J) R)
    (he : core c.radical (alpha c.radical) = U c.radical (alpha c.radical)) :
    CoreReconstruction L :=
  d.coreReconstruction_of_core_image_eq (SourceData.core_image_eq_of_reduced_core_eq_U d h c he)

/-- Both intrinsic block conclusions now require only the actual reduced
core equality supplied by the symplectic critical-distance argument. -/
theorem SourceData.ms_block_of_reduced_core_eq_U
    (c : CharacteristicReduction (L.subgroupOf J) R)
    (he : core c.radical (alpha c.radical) = U c.radical (alpha c.radical)) :
    IsBlock L ∧ IsAlternatingBlock L 6 :=
  d.intrinsic_ms_block_of_coreReconstruction h
    (SourceData.coreReconstruction_of_reduced_core_eq_U d h c he)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
