module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne

/-!
# The distance-four radius facts from the early source conclusions

The marked flag calculation in `RankOne` proves the radius-derived equality,
core containment and edge-star commutator bound. The geometric and commutator
proofs in `Basic` then construct the starred commutator and intersection and
the core/moving equality, retaining the given EarlyFacts.

`radiusFacts` constructs all of RadiusFacts from LocalSource, Geometry,
CommonFacts, b = 4 and EarlyFacts. The earlier (4.6.1)--(4.6.7) conclusions
remain an explicit input; their construction and the later core-center
identification belong to the parent distance-four assembly.

Source: MS93 (1993), (4.6.8)--(4.6.10), pp.905--908, and p.909.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags
variable {M : Type*} [Group M] {R : Subgroup M}

/-- Assemble all radius facts once the three rank-one conclusions have been proved. -/
theorem radiusFacts_of_rankOne [Finite M] {L : Subgroup M} (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (rankOne : RankOneConclusions R geometry) :
    RadiusFacts R geometry where
  toEarlyFacts := early
  radius_derived := rankOne.radius_derived
  core_le_radius := rankOne.core_le_radius
  star_commutator := fun a b ha hab => star_commutator_eq_U geometry early
    common.large_distance a b ha hab (rankOne.radius_derived a ha)
    (rankOne.edge_commutator_le a b ha hab)
  star_intersection := by
    intro a b ha hab
    apply le_antisymm
    · exact star_intersection_le_Z common early a b ha
        (rankOne.radius_derived a ha) (rankOne.core_le_radius a ha)
        (star_commutator_le_of_edge geometry common.large_distance a b ha
          (rankOne.edge_commutator_le a b ha hab))
    · exact le_inf (Z_le_star geometry early common.large_distance a b ha hab)
        (Z_le_B geometry a (geometry.V_local a ha
          (by rw [geometry.distance_constant a ha]; exact common.large_distance)))
  core_eq_moving := fun a ha => core_eq_moving_of_le_radius source geometry
    common.large_distance a ha (rankOne.core_le_radius a ha)

/-- The binary radius conclusions of MS93 (4.6.8)--(4.6.10), together with
the core/moving equality used on p.909. The marked rank-one calculation
discharges all three inputs to `radiusFacts_of_rankOne`; only the earlier
source conclusions remain explicit. -/
theorem radiusFacts [Finite M] {L : Subgroup M} (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry) :
    RadiusFacts R geometry :=
  radiusFacts_of_rankOne source geometry common early
    (rankOneConclusions source geometry common hb early)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags
