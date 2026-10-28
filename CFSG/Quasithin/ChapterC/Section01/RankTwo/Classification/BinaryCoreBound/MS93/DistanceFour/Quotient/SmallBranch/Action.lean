module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Action.Descent
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Action.Midpoint

/-!
# The small-branch core action

The actual finite binary core quotient, its descended SL3(2) action,
faithfulness and full commutation are constructed in `Action.Descent`.
The midpoint geometry supplies an elementary actor of order four and a
fixed-preimage index at most four on core_alpha/U_alpha. Thus the
small-intersection hypothesis gives an offender for this very action.
`exists_coreModule` assembles the quotient and its FF-action with every
midpoint premise discharged. Natural coordinates and purity remain separate
steps in the recognition of the single quotient.

Source: Meierfrankenfeld--Stellmacher (1993), (1.4), p.842, and
(4.6.9)--(4.6.11), pp.908--909.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

include common radius in
/-- The small-intersection branch supplies the actual finite binary core/U
quotient with its faithful, fully moving FF-action under the given projection. -/
theorem exists_coreModule (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hs : s.SmallIntersection) :
    Nonempty (CoreModule source) := by
  exact exists_coreModule_of_midpoint common radius s
    (midpointFacts source geometry common radius hb s hs)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
