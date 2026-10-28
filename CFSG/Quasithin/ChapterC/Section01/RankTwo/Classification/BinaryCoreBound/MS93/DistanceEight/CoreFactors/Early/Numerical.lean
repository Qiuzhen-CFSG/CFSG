module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Moving
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Numerical.SourceCenterBound.DistanceGreaterFour.FixedFactor

/-!
# Applying the moving-span witness to the numerical consumer

The extended critical path constructs the actual moving span. Applying the
existing central-displacement estimate therefore bounds H_a by four using
only the explicit preceding (4.4) outputs. The estimate no longer requires
an additional choice of a moving neighbor or a span-containment premise.
The equality in (4.5.1)(v) still requires the lower bound of four.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1)(v), printed p.896.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Discharge the numerical consumer's moving-span premise from the actual earlier inputs. -/
theorem H_card_le_four (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (ha : color R a = false) :
    Nat.card (H R a) ≤ 4 := by
  obtain ⟨c, _, hd, hspan⟩ := exists_moving_span source common earlier ha
  exact Numerical.SourceCenterBound.DistanceGreaterFour.H_card_le_four_of_moving_span
    common ha (by rw [SimpleGraph.dist_comm]; exact hd) hspan (earlier.centrality a ha)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
