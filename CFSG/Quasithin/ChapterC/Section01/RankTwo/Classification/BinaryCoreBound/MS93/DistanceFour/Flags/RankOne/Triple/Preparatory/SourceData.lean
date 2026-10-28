module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Geometry

/-!
# The source preparatory configuration for MS93 (4.6.8)

This is the configuration at the end of printed p.906: a critical endpoint
and midpoint through beta, propagation of the midpoint commutator bound,
the two incident choices, the nonzero barred triple and the displacement
bound. All actors, kernels and layers are the actual marked constructions
from `Triple.Geometry`.

The selection between (3) and (4) uses the first full parabolic and has
target Z_alpha. This source record records that bound separately from the
legacy `FlagPreparatoryData`. Its construction in `Triple.Preparatory`
combines the critical configuration with the proved propagation and incident
packages, leaving only the original natural-section hypothesis explicit.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), printed p.906, numbered claims (2)--(4) and their selections.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The source configuration before the binary auxiliary-layer argument,
with the printed first-actor bound in the delta0 selection. -/
structure SourceFlagPreparatoryData (source : LocalSource L R) (geometry : Geometry R)
    (i : Bool) where
  middle : Vertex R
  endpoint : Vertex R
  critical : CriticalPair R (alpha R) endpoint (geometry.exists_critical (alpha R) rfl)
  middle_neighbor : Adjacent R (beta R) middle
  first_distance : (cosetGraph R).dist (alpha R) middle = 2
  second_distance : (cosetGraph R).dist middle endpoint = 2
  middle_triple : ¬ ⁅⁅Z R middle, flagResidual source i⁆, V R (alpha R)⁆ ≤
    (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype
  delta2 : M
  delta2_neighbor : flagIncident source i 1 delta2
  endpoint_crosses : ¬ Z R endpoint ⊓ localFlagKernel source (!i) delta2 ≤ Q R (alpha R)
  propagation : ⁅Z R middle, Q R (alpha R)⁆ ≤ U R (alpha R) →
    ∀ t, nu R geometry (alpha R) t → ⁅Z R t, Q R (alpha R)⁆ ≤ U R (alpha R)
  second_triple : ¬ ⁅⁅V R (beta R), localFlagKernel source (!i) delta2⁆,
    localFlagResidual source (!i) delta2⁆ ≤ Z R (alpha R)
  delta0 : M
  delta0_neighbor : flagIncident source i 1 delta0
  endpoint_not_le : ¬ Z R endpoint ≤ localFlagKernel source (!i) delta0
  intersection_commutator :
    ⁅Z R middle ⊓ secondFlagLayer source i delta0, flagParabolic source i⁆ ≤
      Z R (alpha R)
  middle_not_le : ¬ Z R middle ≤ secondFlagLayer source i delta0
  displacement : 2 ≤ (Q R middle).relIndex (secondFlagLayer source i delta0)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
