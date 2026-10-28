module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.Inner
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Exceptional

/-!
# Assembly reductions for the placement of the rank-one component

The theta case, the centerless inner-action case, and the exceptional-center
contradiction together prove containment after the source model comparison.
The inner case constructs its projection and solvable preimage; the exceptional
case reuses the center calculation, which requires only relative normality.

This module does not yet prove 15.3.27(1–2). The nonnormal orbit/Borel
construction and the A.3.18/B.5.6 comparison, including their actual FF and
SQTK hypotheses, remain prerequisites. The displayed comparison is an
intermediate output to be proved from those classifications, not a substitute
for either book theorem. Final placement assembly remains in this module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.27, printed pp.1130–1131 (PDF pp.1147–1148).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement
variable {G : Type*} [Group G] [Finite G]

/-- Sufficient intrinsic consequences of the source model comparison.
The source producer must establish this disjunction using the actual model
isomorphisms. Neither normality nor the comparison is asserted here. -/
theorem yplus_le_component_of_comparison
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (h : RankOneFacts d I)
    (hcontrol : SolvableInvariantControl d I)
    (hn : (c.L.subgroupOf I).Normal)
    (h6 : theta (d.MI I) = d.Yplus)
    (hcases : c.L = theta I ∨
      (center (d.starImage I c.L) = ⊥ ∧
        ∀ y : d.starImage I d.Yplus, ∃ l : d.starImage I c.L,
          ∀ x : d.starImage I c.L,
            (l : d.Star I) * x * l⁻¹ = y * x * y⁻¹) ∨
      Nat.card (center (d.starImage I c.L)) = 3) : d.Yplus ≤ c.L := by
  rcases hcases with htheta | ⟨hz, hi⟩ | hcenter
  · exact yplus_le_of_theta d h6 htheta.ge
  · exact yplus_le_component_of_inner_star_action d hI c h hcontrol hn h6 hz hi
  · exact (component_star_center_card_ne_three d hI c h hcontrol hn hcenter).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement
