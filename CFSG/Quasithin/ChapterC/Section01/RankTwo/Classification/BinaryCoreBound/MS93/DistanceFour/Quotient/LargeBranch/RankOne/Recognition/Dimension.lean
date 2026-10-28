module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Candidate
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Source

/-!
# The source starred dimension and midpoint-seed construction

Source assembles the endpoint and Y-span estimates, the two natural
constituents and full-rank-one coordinates, and the p.912 midpoint-kernel
calculation. It proves starred dimension six and constructs the literal
canonical seed from the source hypotheses and the explicit clause-(4)
escape. Its recognition consumer discharges the dimension/seed callback,
retaining only the independently owned escape construction.

The existing conditional application below remains available: supplied
natural copies and midpoint containments feed Candidate and the checked
clause (3), preserving the marked dual quotient. The original starred escape
has not been removed from the new source construction.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(3)--(5), pp.910--912.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Apply the canonical seed to clause (3). The natural coordinates and the
midpoint containments remain explicit upstream obligations. The quotient
uses exactly the dual of common.natural.marking through Seed recognition. -/
theorem recognition_of_natural_copies_and_midpoint_kernel
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s) (n : NaturalCopies (geometry := geometry) d f)
    (hline : d.subspace (Z R s.middle) ≤ Seed.secondTildeStar (geometry := geometry) d f 1)
    (hspan : midpointSpan f s.middle ≤ Q R s.middle) :
    orbitSpan s.middle ≤ Q R s.middle ∧ Nonempty (SpanQuotient source common s.middle) := by
  obtain ⟨x, _⟩ := canonical_input common radius s hs d f n hline hspan
  exact (Seed.conjugate_seed_recognition common radius hb s hs hbc d f hf x).2

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
