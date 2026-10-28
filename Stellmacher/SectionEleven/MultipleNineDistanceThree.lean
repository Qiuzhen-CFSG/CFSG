module
public import Stellmacher.SectionEleven.MultipleNineDistanceOneExclusion
public import Stellmacher.SectionNine.LemmaNineTen

/-!
# Critical distance three in the commuting Sylow terminal branch

When all ambient two-local subgroups are solvable of characteristic-two
type, a commuting Sylow terminal critical pair has length three. The graph
remains on the generated join, and the local solvability assumption remains
on the original ambient group.

The proved ambient (9.10) gives length at most three. The distance-one
normalizer obstruction excludes one, and (7.5) gives oddness. The existing
arithmetic reduction therefore gives exactly three. This is the Section
Eleven input to (10.1), with no conditional distance-bound hypothesis.

Source: Stellmacher, Journal of Algebra 190 (1997), Section Eleven, pp.66–67,
using (7.5), (9.1)(c) and (9.10).
-/

namespace Stellmacher.SectionEleven
open Later SectionsFiveToSeven SectionNine
universe u
public theorem multiple_nine_distance_three
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {P1 P2 : Subgroup H}
    (ctx : SylowTerminalContext H S0 P1 P2)
    (hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥) :
    ctx.criticalPath.length = 3 := by
  exact multiple_nine_distance_three_of_bound_and_ne_one ctx hcomm
    (lemma_nine_ten_ambient (ctx.toSectionNineContext hcomm))
    (multiple_nine_distance_ne_one ctx hLocal hcomm)
end Stellmacher.SectionEleven
