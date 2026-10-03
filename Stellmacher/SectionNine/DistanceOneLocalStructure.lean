module

public import Stellmacher.SectionNine.DistanceOneLocalStructureAfterCoreEquality
public import Stellmacher.SectionNine.DistanceOneFinalCoreIntersection
/-!
# Local structure with only the initial core equality remaining

The actual ambient distance-one context, faithful initial action and equality
Q_a=Z_a imply the complete local conclusion. Choose the proved extraction,
derive its final source(8) core intersection from the faithful data, and feed
both into the complete local-structure assembly. No extraction, intersection,
terminal quotient or arbitrary elementary subgroup remains as an input.

This thin assembly implements Stellmacher(9.1), Journal of Algebra190 (1997),
p.48 after (11). The chief-factor argument supplies the remaining core
equality, while the faithful producer handles the earlier action calculation.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later
universe u
public theorem distance_one_local_conclusion_of_core_eq_center
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length=1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hcore : QAt ctx.Γ ctx.criticalPath.a=ZAt ctx.Γ ctx.criticalPath.a) :
    DistanceOneLocalConclusion ctx.toLocalContext := by
  obtain ⟨data⟩ := distance_one_initial_geometry ctx hb
  exact distance_one_local_structure_of_core_eq_center ctx hb hfaith hcore data
    (distance_one_final_core_intersection ctx hb hfaith data)
end Stellmacher.SectionNine
