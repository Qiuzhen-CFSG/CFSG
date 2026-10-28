module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Source

/-!
# Full source orbit-span recognition

The clause-(4) escape theorem supplies the actual compatible frame. The
clause-(5) estimates then give dimension six and the midpoint seed. Applying
conjugate-seed recognition returns the literal dual quotient of the orbit
span, its containment in the midpoint kernel, and starred relative index 64.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12)(1)--(5), printed pp.910--912. The distinct passage from
this Z_alpha quotient to the U_alpha kernel remains with FirstFactor.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- All source clauses for the actual span recognition, with no additional
escape, dimension, natural-copy or seed premise. -/
theorem source_spanRecognition
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) : SpanRecognition source common :=
  spanRecognition_of_source_star_escape common radius hb
    (fun s hs hbc d => Escape.source_second_star_escape common radius hb s hs hbc d)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
