module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.FourImageSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.EightImageSource

/-!
# Original MS93 prescribed critical-path replacement

The proved predecessor-image-four and predecessor-image-eight branches
discharge backward switching under the full failed-span hypotheses. Two
regular turns place the backward edge in the natural group four vertices
earlier. The escaping radius centralizes both order-four edge planes, so
faithfulness of the natural action identifies them.

The existing source-specific recurrence and terminal contradiction then
give (4.4.4) from CommonFacts and b > 4. For each prescribed adjacent edge,
the same element of the starting stabilizer carries the first edge to that
edge and carries Z at position two outside the kernel at position b-2.
Both maps use conjugation by the inverse, matching the source convention
X^g = g⁻¹Xg. The normalizer hypothesis is relative to the starting stabilizer.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.4), printed p.894.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.OriginalSource
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Backward switching with both remaining source image cases discharged. -/
theorem failedSpanSwitching (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) : FailedSpanSwitching R geometry :=
  failedSpanSwitching_of_large_image_cases common hb
    (FourImageSource.failedSpanLargeImageSwitching_four common hb)
    (EightImageSource.failedSpanLargeImageSwitching_eight common hb)

/-- Original (4.4.4): prescribed replacement on every regular critical path,
with one conjugator for both clauses and no additional switching premise. -/
theorem prescribedReplacement (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hp : HasTurnConjugators R p) : PrescribedReplacement R p :=
  SourceCritical.prescribedReplacement common hb (failedSpanSwitching common hb) p hp

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.OriginalSource
