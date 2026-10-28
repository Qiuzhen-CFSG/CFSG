module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Marked
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences

/-!
# Binary rank-one conclusions for the MS93 distance-four argument

The edge-radius layer is elementary abelian and has a characteristic
pullback to the original edge group. Marked parabolic core selection therefore
constructs its actual parabolic conjugation action. The source-ordered
residuals generate the vertex component, and conjugation covariance reduces
the three rank-one radius conclusions to the distinguished edge.

`rankOneConclusions` constructs the marked flag selection and (4.6.8)
triple bound, applies the (4.6.9) displacement and edge-generator
calculation, and transports the resulting distinguished-edge conclusions.
It proves the radius-derived equality, core containment and edge-star
commutator bound from the supplied common and early facts with b = 4.
The larger RadiusFacts assembly remains in `Flags`.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8)--(4.6.9), printed pp.905--908.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags

variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The three binary rank-one radius conclusions of MS93 (4.6.8)--(4.6.9).
The marked flag control and distinguished-edge conclusions are constructed
from the source inputs before transport to every M-vertex and adjacent edge. -/
theorem rankOneConclusions [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry) :
    RankOneConclusions R geometry :=
  RankOne.rankOneConclusions_of_base geometry early
    (RankOne.baseConclusions source geometry common hb early
      (RankOne.flagControl source geometry common hb early))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags
