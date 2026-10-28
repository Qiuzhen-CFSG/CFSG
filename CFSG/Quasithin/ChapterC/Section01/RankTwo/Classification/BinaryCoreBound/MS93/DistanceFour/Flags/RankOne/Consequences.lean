module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Marked
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.EdgeComparison

/-!
# Conditional assembly for the MS93 distance-four consequences

The flag output of (4.6.8) gives the critical-path covering and identifies
the literal quotient centralizer Bzero with B_alpha. This equality supplies
the edge-generator comparison, which bounds the edge-star commutator and
determines the derived radius group. The covering gives core containment.

Thus baseConclusions proves the three distinguished-edge consequences
from CommonFacts, EarlyFacts and the exact conditional input FlagControl.
The parent rank-one assembly constructs FlagControl and transports these
conclusions to all vertices and edges.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9), printed p.908.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The distinguished-edge consequences of MS93 (4.6.9), conditional only
on the preceding common, early and flag outputs. -/
theorem baseConclusions [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (control : FlagControl source) : BaseConclusions R geometry := by
  obtain ⟨displacement, hzero⟩ :=
    localDisplacement_and_Bzero source geometry common hb early control
  exact baseConclusions_of_displacement_comparison source geometry common early
    displacement (edgeGeneratorComparison source geometry common hb early control hzero)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
