module
public import Stellmacher.SectionNine.NineThreeNativeActionRank

/-!
# The order-sixteen intermediate conclusion in (9.3)

This preserves the cardinality-only interface for the actual normalized
configuration under nontrivial native Thompson action. The shared canonical
rank theorem proves the local quotient inputs, removes the fixed complement
using (7.5), and applies (1.7) with the geometric fixed-index bound. Its
center-cardinality field is the desired conclusion; the same rank data also
feed wreath recognition.

Source: Stellmacher (9.3), Journal of Algebra 190 (1997), p.50,
`refs/files/stellmacher-n-group.pdf`. Native nontriviality is explicit, and
this intermediate order sixteen is not the final numbered (9.3) conclusion.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_native_action_card_sixteen
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hJnative : ¬ elementaryAbelianMaxJ T ≤
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)) :
    Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 16 := by
  exact (nine_three_native_action_rank_data ctx hb hlarge first second config hJnative).center_card

end Stellmacher.SectionNine
