module
public import Stellmacher.SectionTen.TenOneIntersectionNormalization
public import Theory.GroupAction.SubgroupQuotientSupportLift
public import Theory.GroupAction.SubgroupQuotientCommutatorImage
public import Theory.GroupAction.ActorSubtypeCommutator
public import Theory.GroupAction.NormalizingActor

/-!
# Normalization of the enlarged selected displacement

For the actual length-three Section Ten path, retain a supplied conjugation
action on the terminal quotient V/Z. Suppose the selected first-module actor
has displacement containing the first center and its cyclic image is
normalized by the middle-core image. Then the full middle stabilizer
normalizes the ambient displacement enlarged by the middle center.

The literal quotient displacement lifts to the ambient displacement joined
with the terminal center. The selected first line and center splitting make
this the join with the middle center. Normalization of the cyclic actor image
preserves its quotient displacement, hence the middle core normalizes that
lift. The common-intersection normalization transfer supplies the full middle
stabilizer. No alternate quotient action or additional rank assumption is used.

This proves the normalization transfer in Stellmacher (10.1)(13), printed
p.63 of `refs/files/stellmacher-n-group.pdf`; the separate actor-normality
producer supplies its action-image hypothesis in the final assembly.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_displacement_normalized_of_actor_image_normalized
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a',
      ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
        QuotientGroup.mk'
          ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
          ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp
              (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
                point).mp point.property⟩)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor:G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hselected : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      ⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor:G)⁆)
    (hnorm : ((QAt ctx.Γ middle).subgroupOf (GAt ctx.Γ ctx.criticalPath.a')).map
      action.rangeRestrict ≤ Subgroup.normalizer
        (Subgroup.zpowers (action.rangeRestrict actor) : Set action.range)) :
    GAt ctx.Γ middle ≤ Subgroup.normalizer
      ((⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor:G)⁆ ⊔
        ZAt ctx.Γ middle : Subgroup G) : Set G) := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let Qm := QAt ctx.Γ middle
  let I := VAt ctx.Γ ctx.criticalPath.firstStep ⊓ V
  let U := GeneratedNeighborhoodV ctx.Γ middle
  let C := Subgroup.zpowers (actor:G)
  let D := ⁅V,C⁆
  let L := D ⊔ Z
  let W := V ⧸ Z.subgroupOf V
  let R := (Qm.subgroupOf P).map action.rangeRestrict
  let J := Subgroup.zpowers (action.rangeRestrict actor)
  let Dbar := commutatorAction J W
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hVW : V ≤ U := le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,rfl⟩
  have hfirstU : VAt ctx.Γ ctx.criticalPath.firstStep ≤ U :=
    le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst,rfl⟩
  have hDI : D ≤ I := by
    apply le_trans ?_ (ten_one_generated_derived_le_intersection ctx middle hpath)
    rw [show DerivedAmbient U = ⁅U,U⁆ from Subgroup.map_subtype_commutator U]
    exact Subgroup.commutator_mono hVW ((Subgroup.zpowers_le.mpr hactor).trans hfirstU)
  have hZmiddleI : ZAt ctx.Γ middle ≤ I := le_inf
    (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst))
    (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal))
  have hZjoin : ZAt ctx.Γ middle = ZAt ctx.Γ ctx.criticalPath.firstStep ⊔ Z :=
    (sectionTenOpeningData ctx middle hpath).center_direct_product.1
  have hZmL : ZAt ctx.Γ middle ≤ L := by
    rw [hZjoin]
    exact sup_le (hselected.trans le_sup_left) le_sup_right
  have hZmid : Z ≤ ZAt ctx.Γ middle := by rw [hZjoin]; exact le_sup_right
  have hLI : L ≤ I := sup_le hDI (hZmid.trans hZmiddleI)
  have hL : D ⊔ ZAt ctx.Γ middle = L := le_antisymm (sup_le le_sup_left hZmL)
    (sup_le le_sup_left (hZmid.trans le_sup_right))
  have hPV : P ≤ Subgroup.normalizer (V : Set G) :=
    stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a'
  have hQP : Qm ≤ P := ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core
    middle ctx.criticalPath.a' ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal) default).2.2
  have hCP : C ≤ P := Subgroup.zpowers_le.mpr actor.property
  have hCV : D ≤ V := hDI.trans inf_le_right
  have hZV : Z ≤ V := hZmid.trans (hZmiddleI.trans inf_le_right)
  have hCnative : C.subgroupOf P = Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hCP,MonoidHom.map_zpowers]
    rfl
  have hDbar : Dbar = (D.subgroupOf V).map (QuotientGroup.mk' (Z.subgroupOf V)) := by
    rw [show Dbar = commutatorAction J W from rfl,← commutatorAction_map_actor_subtype action.range J,
      MonoidHom.map_zpowers]
    have hh := Subgroup.quotient_conjugation_commutatorAction_eq_image P V Z C hPV hCP hN action hformula
    rw [hCnative,MonoidHom.map_zpowers] at hh
    exact hh
  have hLift : (Dbar.comap (QuotientGroup.mk' (Z.subgroupOf V))).map V.subtype = L := by
    rw [hDbar,Subgroup.comap_map_eq,QuotientGroup.ker_mk',Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hCV,Subgroup.map_subgroupOf_eq_of_le hZV]
  have hInv := commutatorAction_isInvariant_of_normalizing_actor (V:=W) R J hnorm
  have hpreserve (mover:P) (hmover:(mover:G)∈Qm) : Dbar.map (action mover).toMonoidHom = Dbar := by
    let r : R := ⟨action.rangeRestrict mover,Subgroup.mem_map_of_mem action.rangeRestrict hmover⟩
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      exact (hInv.invariant r v).mp hv
    · intro v hv
      refine ⟨(action mover)⁻¹ v, ?_, ?_⟩
      · exact (hInv.invariant r⁻¹ v).mp hv
      · exact (action mover).apply_symm_apply v
  have hQnorm : Qm ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hLift]
    exact Subgroup.lift_support_normalizes P V Z Qm hQP hPV action hformula Dbar hpreserve
  change GAt ctx.Γ middle ≤ Subgroup.normalizer ((D ⊔ ZAt ctx.Γ middle : Subgroup G) : Set G)
  rw [hL]
  exact ten_one_intersection_subgroup_normalized ctx middle hpath L hZmL hLI hQnorm
end Stellmacher.SectionTen
