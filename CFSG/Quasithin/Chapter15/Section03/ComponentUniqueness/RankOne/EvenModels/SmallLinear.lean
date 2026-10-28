module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.SmallModels

/-!
# The small linear cases of the S₃ exclusion

In PSL₃(2) every four-group is self-centralizing, by the genuine exceptional
isomorphism with PSL₂(7). In PSL₂(4), the specified four-group is a whole
Sylow subgroup and the matrix centralizer calculation applies. The original
actor is therefore A₄ in both cases, contradicting 15.3.43(d).

The exceptional isomorphism and its ATLAS attribution are retained in
`Theory.SpecificGroups.PSL3.BinaryComparison` through the imported model
calculation. Neither branch assumes a parabolic or actor identification.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.43, printed p.1140.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

/-- The actual binary degree-three component is impossible. -/
theorem not_linear_three_binary (hm : ClassicalGroup.IsPSL L 3 2) : False := by
  let : IsKleinFour V₂ := plane_isKleinFour c
  exact false_of_plane_centralizer c
    (RankTwo.RankOnePlane.binary_plane_selfCentralizing hm (plane_le_component c))

/-- The actual degree-two model over the four-element field is impossible. -/
theorem not_linear_two_four (hm : ClassicalGroup.IsPSL L 2 4) : False := by
  obtain ⟨P, hP⟩ := component_sylow c
  exact false_of_plane_centralizer c
    (RankTwo.RankOnePlane.linear_four_plane_selfCentralizing hm P hP
      c.plane_two_le (plane_le_component c) c.plane_two_card)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
