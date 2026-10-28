module
public import Stellmacher.SectionNine.NineThreeNativeActionRank
public import Stellmacher.SectionOne.TwoFactorWreathRecognition

/-!
# The canonical wreath quotient in the order-sixteen branch of (9.3)

With the actual normalized extraction pair and nontrivial native Thompson
action, the canonical faithful quotient acting on the initial center is
isomorphic to the literal SL₂(2) wreath C₂ model. The shared rank theorem
retains its exact elementary module, Section One hypotheses, local Sylow
generation and unique maximality, and two canonical factors. The two-factor
recognition theorem applies directly to those data.

This is the intermediate barred-group conclusion on p.50 of Stellmacher
(9.3), Journal of Algebra 190 (1997), `refs/files/stellmacher-n-group.pdf`.
The quotient here is the canonical center-action quotient; the statement
makes no additional identification of its kernel with the whole initial
core, and it does not assert the final contradiction or numbered (9.3).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_native_action_wreath
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
    Nonempty (SectionSixBarP1 ctx.hypothesisTwo ≃* SL2TwoWreathC2) := by
  have hrank := nine_three_native_action_rank_data ctx hb hlarge first second config hJnative
  let _ := hrank.elementary
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  exact SectionOne.oneSeven_wreath_of_two_factors hrank.action_hypotheses
    (sectionSixBarSylow ctx.hypothesisTwo) hrank.generated hrank.unique_maximal hrank.factor_count

end Stellmacher.SectionNine
