module

public import Stellmacher.SectionNine.NineThreeMixedOrder

/-!
# Native transport of the barred involution plane

The canonical Section Six quotient action lifts to literal conjugation
through the actual stabilizer image. This transports the barred centralizer
orbit and Sylow-fixed vector in Stellmacher (9.3), printed p.50, without
claiming that a quotient centralizer lifts to a native actor centralizer.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_barred_actor_native_representative
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (actor : SectionSixBarP1 ctx.hypothesisTwo) :
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    ∃ representative : P1, ∃ conjugator ∈ GAt ctx.Γ ctx.criticalPath.a,
      sectionSixQuotientMap ctx.hypothesisTwo representative = actor ∧
      embedding conjugator = (representative : H) ∧
      ∀ vector : sectionSixLocalV ctx.hypothesisTwo,
        ((actor • vector : sectionSixLocalV ctx.hypothesisTwo) : P1).val =
          (MulAut.conj (embedding conjugator)) ((vector : P1) : H) := by
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  let quotient := sectionSixQuotientMap ctx.hypothesisTwo
  have hsurj : Function.Surjective quotient := QuotientGroup.mk'_surjective _
  have hkernel : quotient.ker = SectionTwo.cSubgroup (sectionSixSylow ctx.hypothesisTwo) :=
    QuotientGroup.ker_mk' _
  obtain ⟨representative, hrepresentative⟩ := hsurj actor
  have hgroup : (GAt ctx.Γ ctx.criticalPath.a).map embedding = P1 :=
    (nine_two_ambient_setup ctx).2.1
  have hmem : (representative : H) ∈ (GAt ctx.Γ ctx.criticalPath.a).map embedding := by
    rw [hgroup]
    exact representative.property
  obtain ⟨conjugator, hconjugator, hembedding⟩ := Subgroup.mem_map.mp hmem
  refine ⟨representative, conjugator, hconjugator, hrepresentative, hembedding, ?_⟩
  intro vector
  have haction := SectionTwo.quotientConjugationAction_smul_coe
    (sectionSixSylow ctx.hypothesisTwo) quotient hsurj hkernel representative vector
  have hambient := congrArg P1.subtype haction
  simpa [sectionSixQuotientAction, hrepresentative, hembedding, MulAut.conj_apply] using hambient

public theorem nine_three_mixed_native_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (rank : NineThreeNativeActionRankData ctx) :
    let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let plane := (⁅ZAt ctx.Γ ctx.criticalPath.a,
      ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    plane ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ ∧
      ∀ vector ∈ plane, vector ≠ 1 → ∀ target ∈ plane, target ≠ 1 →
        ∃ conjugator ∈ GAt ctx.Γ ctx.criticalPath.a,
          (MulAut.conj conjugator) vector = target := by
  let _ := rank.elementary
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let actor := ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a
  let plane := (⁅ZAt ctx.Γ ctx.criticalPath.a, actor⁆ : Subgroup G)
  let moduleGroup := sectionSixLocalV ctx.hypothesisTwo
  let quotient := sectionSixQuotientMap ctx.hypothesisTwo
  let inclusion := P1.subtype.comp moduleGroup.subtype
  let barActor := ((actor.map embedding).subgroupOf P1).map quotient
  let sylow := sectionSixBarSylow ctx.hypothesisTwo
  have htransport := nine_three_barred_actor_action_transport ctx actor
    (nine_three_mixed_actor_quadratic ctx hb first second config).1
  have hgeneration := nine_three_mixed_order_and_barred_generation
    ctx hb hlarge first second config rank
  have hplane := SectionOne.oneSeven_two_factor_involution_plane
    rank.action_hypotheses sylow rank.generated rank.unique_maximal rank.fixed_product_eq_bot
    rank.factor_count barActor htransport.1 hgeneration.2.1 hgeneration.2.2
  have hcomm : (commutatorAction barActor moduleGroup).map inclusion = plane.map embedding :=
    htransport.2.2
  have hbarT : ((T.map embedding).subgroupOf P1).map quotient =
      (sylow : Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) := by
    have hlocal : (T.map embedding).subgroupOf P1 =
        (sectionSixSylow ctx.hypothesisTwo : Subgroup P1) := by
      apply (Subgroup.map_injective P1.subtype_injective)
      rw [Subgroup.map_subgroupOf_eq_of_le, ctx.map_S,
        (sectionSix_barred_action_setup ctx.hypothesisTwo).sylow_image]
      rw [ctx.map_S]
      exact ctx.hypothesisTwo.fiveOne.P1_mem.1.2.1.1
    rw [hlocal]
    rfl
  have hfixed : (FixedPoints.subgroup
      (sylow : Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) moduleGroup).map inclusion =
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (T : Set G)).map embedding := by
    have htransportT := (nine_three_barred_actor_action_transport ctx T le_rfl).2.1
    change (FixedPoints.subgroup (((T.map embedding).subgroupOf P1).map quotient)
      moduleGroup).map inclusion = _ at htransportT
    rw [hbarT] at htransportT
    exact htransportT
  constructor
  · obtain ⟨fixed, hfixedNe⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hplane.2.2.1
    obtain ⟨native, hnative, hnativeImage⟩ := Subgroup.mem_map.mp
      (hcomm ▸ Subgroup.mem_map_of_mem inclusion fixed.property.1)
    obtain ⟨central, hcentral, hcentralImage⟩ := Subgroup.mem_map.mp
      (hfixed ▸ Subgroup.mem_map_of_mem inclusion fixed.property.2)
    have heq : native = central := ctx.embedding_injective (hnativeImage.trans hcentralImage.symm)
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    refine ⟨⟨native, hnative, heq ▸ hcentral.2⟩, ?_⟩
    intro hidentity
    apply hfixedNe
    apply Subtype.ext
    apply P1.subtype_injective.comp moduleGroup.subtype_injective
    have hnativeOne := congrArg Subtype.val hidentity
    change native = 1 at hnativeOne
    change inclusion (fixed : moduleGroup) = inclusion 1
    rw [← hnativeImage, hnativeOne, map_one, map_one]
  · intro vector hvector hvectorNe target htarget htargetNe
    obtain ⟨barVector, hbarVector, hvectorImage⟩ := Subgroup.mem_map.mp
      (hcomm.symm ▸ Subgroup.mem_map_of_mem embedding hvector)
    obtain ⟨barTarget, hbarTarget, htargetImage⟩ := Subgroup.mem_map.mp
      (hcomm.symm ▸ Subgroup.mem_map_of_mem embedding htarget)
    have hbarVectorNe : barVector ≠ 1 := by
      intro heq
      apply hvectorNe
      apply ctx.embedding_injective
      simpa only [heq, map_one] using hvectorImage.symm
    have hbarTargetNe : barTarget ≠ 1 := by
      intro heq
      apply htargetNe
      apply ctx.embedding_injective
      simpa only [heq, map_one] using htargetImage.symm
    obtain ⟨barConjugator, hcentralizer, haction⟩ := hplane.2.2.2
      barVector hbarVector hbarVectorNe barTarget hbarTarget hbarTargetNe
    obtain ⟨representative, conjugator, hconjugator, hquotient, hembedding, hconj⟩ :=
      nine_three_barred_actor_native_representative ctx barConjugator
    refine ⟨conjugator, hconjugator, ctx.embedding_injective ?_⟩
    have hconjugate := hconj barVector
    change inclusion (barConjugator • barVector) =
      (MulAut.conj (embedding conjugator)) (inclusion barVector) at hconjugate
    rw [haction, htargetImage, hvectorImage] at hconjugate
    simpa only [MulAut.conj_apply, map_mul, map_inv] using hconjugate.symm

end Stellmacher.SectionNine
