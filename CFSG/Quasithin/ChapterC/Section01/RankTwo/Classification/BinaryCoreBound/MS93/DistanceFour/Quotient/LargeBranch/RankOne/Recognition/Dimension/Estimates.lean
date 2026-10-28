module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Transport

/-!
# Assembly boundary for the endpoint and Y-span estimates

Transport proves the incident fixed-layer inclusion, the unstarred
second-layer inclusion in the literal Y-span, and escape of that span.
It also propagates the source's full-first-actor fixation of Y to the
first ordered residual and to second-core fixation of the whole span.

The remaining inputs below are precisely the endpoint centralizer bound,
the radius bound, that initial fixation of Y, and the two distinct
intersection-case bounds. Their source proofs are still required before
constructing Estimates from the original hypotheses alone. This conditional
assembly does not assert the unconditional source estimates or dimension six.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(5), printed p.911, with the literal layers on p.905.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Assemble the eight literal estimates after the endpoint/Y-fixation and
intersection calculations. The unstarred inclusion, span escape, and both
required fixation conclusions are derived here, not additional premises. -/
theorem estimates_of_endpoint_and_intersection_calculations
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (hendpoint :
      (commutatorPreimage (V R (alpha R)) (Z R s.endpoint) (Z R (alpha R))).relIndex
        (V R (alpha R)) ≤ 4)
    (hradius : (B R (alpha R) (geometry.Z_normal (alpha R))).relIndex
      (V R (alpha R)) ≤ 64)
    (hY : ⁅Sections.fixedPreimage s.middle, (f.actor false).map (embedM R)⁆ ≤ Z R (alpha R))
    (hcrossing : (¬ ySpan f s.middle ⊓ Q R s.middle ≤ Sections.fixedPreimage s.middle) →
      (commutatorPreimage (V R (alpha R)) ((f.core true).map (embedM R))
        (Z R (alpha R))).relIndex (V R (alpha R)) ≤ 4)
    (hcontained : ySpan f s.middle ⊓ Q R s.middle ≤ Sections.fixedPreimage s.middle →
      (Z R (alpha R)).relIndex
        ⁅VStar R geometry (alpha R) (beta R), (f.core false).map (embedM R)⁆ ≤ 4) :
    Estimates d f s := by
  obtain ⟨hfirst, hsecond⟩ := first_actor_fixed_consequences common d f s.middle hY
  exact {
    endpoint_bound := hendpoint
    radius_bound := hradius
    Y_fixed := hfirst
    unstarred_le_span := secondLayer_le_ySpan common radius hb s hbc d f hf
    span_escape := ySpan_escape common radius hb s hbc d f hf hescape
    span_fixed := hsecond
    crossing_bound := hcrossing
    contained_bound := hcontained }

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
