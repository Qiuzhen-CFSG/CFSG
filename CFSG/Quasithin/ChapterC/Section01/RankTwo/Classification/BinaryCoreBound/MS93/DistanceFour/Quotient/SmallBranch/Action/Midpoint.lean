module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Action.Descent
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Action.Midpoint.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Action.Midpoint.OrderFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Action.Midpoint.Transfer

/-!
# The midpoint geometry for the small-intersection branch

The actual radius subgroup at the critical midpoint alpha+2 lies in the
base stabilizer and has elementary abelian image under the given projection.
The source flag and displacement calculation proves that its image has order
four. The small-intersection hypothesis, together with that order calculation,
then gives [core_alpha intersect Q_middle,V_middle] ≤ U_alpha and bounds the
fixed-preimage index in the actual core by four.

`midpointFacts` assembles these results with every additional premise discharged.
It supplies the geometric witness consumed by `Action.Descent` for the actual
core/U action. The printed bound initially concerns V_alpha/Z_alpha; the
separate transfer proof is essential for this core/U conclusion.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9)--(4.6.11), pp.908--909.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

include common radius in
/-- The small-intersection geometry supplies the actual midpoint actor and the
fixed-preimage bound on core_alpha/U_alpha, with no extra geometric premises. -/
theorem midpointFacts (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hs : s.SmallIntersection) :
    MidpointFacts (source := source) s := by
  have hcard := midpointActor_card_four source geometry common radius hb s
  exact {
    locality := midpoint_locality source geometry common s
    elementary := midpointActor_elementary source geometry common radius s
    card := hcard
    fixed_index := midpoint_fixed_index source geometry common radius hb s hs hcard }

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
