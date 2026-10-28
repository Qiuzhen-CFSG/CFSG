module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint.Bounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint.Fixation

/-!
# Endpoint calculation in MS93 (4.6.12)(5)

The supplied quotient and compatible frame give the endpoint fixed-preimage
index at most four and the radius index over B at most 64. The binary auxiliary
displacement has order two; its printed order-four alternative is excluded by
the critical natural-module pairing. The two natural sections and the endpoint
bound then force the full first actor to fix Y modulo Z_alpha. The theorem
below assembles these three conclusions, discharging the fixation calculation's
endpoint-bound premise for the original supplied module and compatible frame.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), printed p.911, using the flag notation on p.905.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The three opening conclusions of MS93 (4.6.12)(5): the endpoint and
radius bounds, and fixation of the literal Y by the full first actor.
The quotient denominator throughout the endpoint and fixation claims is Z_alpha. -/
theorem endpoint_radius_and_Y_fixed
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle) :
    (commutatorPreimage (V R (alpha R)) (Z R s.endpoint) (Z R (alpha R))).relIndex
        (V R (alpha R)) ≤ 4 ∧
      (B R (alpha R) (geometry.Z_normal (alpha R))).relIndex (V R (alpha R)) ≤ 64 ∧
      ⁅Sections.fixedPreimage s.middle, (f.actor false).map (embedM R)⁆ ≤ Z R (alpha R) := by
  obtain ⟨hendpoint, hradius⟩ := endpoint_and_radius_bounds common radius s hbc d f hf hescape
  exact ⟨hendpoint, hradius,
    first_actor_fixed_of_endpoint_bound common radius hb s hs hbc d f hf hendpoint⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
