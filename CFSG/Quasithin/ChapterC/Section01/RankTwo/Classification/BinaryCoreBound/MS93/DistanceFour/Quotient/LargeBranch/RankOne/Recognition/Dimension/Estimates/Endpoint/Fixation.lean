module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint.Bounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint.Fixation.Preparation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint.Fixation.Interface
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint.Fixation.Linear
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint.Fixation.Marked

/-!
# Full first-actor fixation of Y from the endpoint bound

The literal two natural sections force codimension at least four for Y, and
the endpoint bound forces displacement at most two for every involution
of the same marked SL3(2) representation. An actual cubic in the first
parabolic has norm landing in Y. Linear saturation therefore forces this
cubic and an inverting reflection to fix Y pointwise. They generate the
full first actor together with the actual edge image, which fixes Y by
definition, giving the ambient commutator containment modulo Z_alpha.

The theorem applies to any supplied layer module and compatible seed frame.
Only the explicit endpoint index bound remains for the endpoint assembly
to discharge; no cubic data, fixation or dimension premise is required.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(1)--(2), printed
p.910, and the opening of (4.6.12)(5), p.911.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The endpoint fixed-preimage index at most four forces the full first
actor to fix the literal Y modulo Z_alpha, as in MS93 (4.6.12)(5). -/
theorem first_actor_fixed_of_endpoint_bound
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hendpoint :
      (commutatorPreimage (V R (alpha R)) (Z R s.endpoint) (Z R (alpha R))).relIndex
        (V R (alpha R)) ≤ 4) :
    ⁅Sections.fixedPreimage s.middle, (f.actor false).map (embedM R)⁆ ≤ Z R (alpha R) := by
  obtain ⟨cubic⟩ := Fixation.exists_cubicData common radius hb s hbc d f hf
  exact cubic.first_actor_fixed common d f s.middle
    (cubic.fixed_generators_of_endpoint_bound common radius hb s hs hbc d f hendpoint)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
