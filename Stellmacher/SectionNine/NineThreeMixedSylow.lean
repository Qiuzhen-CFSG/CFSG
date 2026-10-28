module
public import Stellmacher.SectionNine.NineThreeMixedOrder
public import Stellmacher.SectionNine.NineThreeMixedNativeLift
public import Stellmacher.SectionNine.NineThreeMixedSylowTransfer

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_mixed_order_two_and_sylow
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
    let R0 := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m,
      ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    Nat.card R0 = 2 ∧ ∃ conjugator : G,
      conjugator ∈ GAt ctx.Γ ctx.criticalPath.a ∧
      T.map (MulAut.conj conjugator).toMonoidHom ≤
        Subgroup.centralizer (R0 : Set G) := by
  let horder := nine_three_mixed_order_and_barred_generation
    ctx hb hlarge first second config rank
  have hnative := nine_three_mixed_native_action ctx hb hlarge first second config rank
  exact nine_three_mixed_order_two_and_sylow_of_action ctx first second config
    horder.1 hnative

end Stellmacher.SectionNine
