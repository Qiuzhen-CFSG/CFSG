module
public import Stellmacher.SectionNine.SourceBarredBaumannReduction
public import Stellmacher.SectionNine.NineThreeNativeActionRank

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_mixed_barred_actor_not_le_oneB
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
    let barY := ((Y.map embedding).subgroupOf P1).map
      (sectionSixQuotientMap ctx.hypothesisTwo)
    ¬ barY ≤ SectionOne.oneB (V := sectionSixLocalV ctx.hypothesisTwo)
      (sectionSixBarSylow ctx.hypothesisTwo :
        Subgroup (SectionSixBarP1 ctx.hypothesisTwo)) := by
  let _ := rank.elementary
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  exact nine_three_source_barred_actor_not_le_oneB ctx hb hlarge first second config

end Stellmacher.SectionNine
