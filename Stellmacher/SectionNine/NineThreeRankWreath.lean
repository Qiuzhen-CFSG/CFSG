module
public import Stellmacher.SectionNine.NineThreeCanonicalActionRank
public import Stellmacher.SectionNine.NineThreeCanonicalOffenderNontrivial
public import Stellmacher.SectionOne.TwoFactorWreathRecognition

/-!
# The unconditional intermediate rank and wreath case in (9.3)

If the initial center in the original ambient Section Nine context has order
larger than four, it has order sixteen and its canonical faithful quotient
is the literal SL₂(2) wreath C₂ group. The conclusion also retains all actual
rank-two action data required for the subsequent centralizer argument.

Construct the two geometric extractions and their selected-Sylow normalization.
The canonical offender theorem proves barred critical nontriviality in both
native-action cases; in the contrary case the actual paired quadratic actor
has fixed index two. Apply (6.4) directly to canonical fixed vectors, then the
geometric index bound and (1.7) yield rank two. Canonical factor recognition
identifies the quotient with the standard wreath group.

This supplies the intermediate paragraph of Stellmacher (9.3), Journal of
Algebra 190 (1997), p.50, `refs/files/stellmacher-n-group.pdf`. No native
Thompson nontriviality is assumed or asserted. The final order-two centralizer
contradiction excluding this intermediate case is a separate remaining step.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_rank_wreath
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a)) :
    NineThreeNativeActionRankData ctx ∧
      Nonempty (SectionSixBarP1 ctx.hypothesisTwo ≃* SL2TwoWreathC2) := by
  obtain ⟨first⟩ := nine_three_first_configuration ctx hb hlarge
  obtain ⟨second⟩ := nine_three_second_configuration ctx hb first
  obtain ⟨config⟩ := nine_three_normalized_geometry ctx hb hlarge first second
  have hJ := nine_three_canonical_offender_nontrivial ctx hb hlarge first second config
  have hrank := nine_three_canonical_action_rank_data ctx hb hlarge first second config hJ
  let _ := hrank.elementary
  let _ := sectionSixQuotientAction ctx.hypothesisTwo
  exact ⟨hrank,SectionOne.oneSeven_wreath_of_two_factors hrank.action_hypotheses
    (sectionSixBarSylow ctx.hypothesisTwo) hrank.generated hrank.unique_maximal hrank.factor_count⟩

end Stellmacher.SectionNine
