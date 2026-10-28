module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Inputs

/-!
# The source incident data on MS93 p.906

This record retains the incident choices and claims (3)--(4) while recording
the printed delta0 selection with the first full actor and target Z_alpha.
The older `FlagLocalData` remains a separate conditional interface.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), printed p.906, especially the selection between (3) and (4).
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The source incident conclusions, with the corrected first-actor bound. -/
structure SourceFlagLocalData (p : FlagCriticalData source geometry i) where
  delta2 : M
  delta2_neighbor : flagIncident source i 1 delta2
  endpoint_crosses : ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) delta2 ≤ Q R (alpha R)
  second_triple : ¬ ⁅⁅V R (beta R), localFlagKernel source (!i) delta2⁆,
    localFlagResidual source (!i) delta2⁆ ≤ Z R (alpha R)
  delta0 : M
  delta0_neighbor : flagIncident source i 1 delta0
  endpoint_not_le : ¬ Z R p.endpoint ≤ localFlagKernel source (!i) delta0
  intersection_commutator :
    ⁅Z R p.middle ⊓ secondFlagLayer source i delta0, flagParabolic source i⁆ ≤
      Z R (alpha R)
  middle_not_le : ¬ Z R p.middle ≤ secondFlagLayer source i delta0
  displacement : 2 ≤ (Q R p.middle).relIndex (secondFlagLayer source i delta0)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
