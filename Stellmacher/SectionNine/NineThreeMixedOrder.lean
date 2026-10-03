module
public import Stellmacher.SectionNine.NineThreeMixedOrderReduction
public import Stellmacher.SectionNine.NineThreeBarredGeneration
public import Stellmacher.SectionOne.TwoFactorInvolutionPlane
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem nine_three_mixed_order_and_barred_generation
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
    letI := rank.elementary
    letI := sectionSixQuotientAction ctx.hypothesisTwo
    let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let Y := ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a
    let R := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m,Y⁆ : Subgroup G)
    let barY := ((Y.map embedding).subgroupOf P1).map (sectionSixQuotientMap ctx.hypothesisTwo)
    let U := sectionSixBarSylow ctx.hypothesisTwo
    Nat.card R = 2 ∧ Nat.card barY = 2 ∧
      (U : Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) =
        SectionOne.oneB (V := sectionSixLocalV ctx.hypothesisTwo) (U : Subgroup _) ⊔ barY := by
  let _ := rank.elementary
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let Y := ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a
  let R := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m,Y⁆ : Subgroup G)
  let barY := ((Y.map embedding).subgroupOf P1).map (sectionSixQuotientMap ctx.hypothesisTwo)
  let U := sectionSixBarSylow ctx.hypothesisTwo
  have hgen := nine_three_mixed_barred_generation ctx hb hlarge first second config rank
  have hbar := nine_three_mixed_barred_actor_card ctx hb hlarge first second config
  have hplaneAction := SectionOne.oneSeven_two_factor_involution_plane
    rank.action_hypotheses U rank.generated rank.unique_maximal rank.fixed_product_eq_bot
    rank.factor_count barY (nine_three_barred_actor_action_transport ctx Y
      (nine_three_mixed_actor_quadratic ctx hb first second config).1).1 hbar hgen
  have hR := nine_three_mixed_order_two_of_canonical_plane_cards
    ctx hb hlarge first second config rank hplaneAction.1 hplaneAction.2.1
  refine ⟨hR, hbar, hgen⟩
end Stellmacher.SectionNine
