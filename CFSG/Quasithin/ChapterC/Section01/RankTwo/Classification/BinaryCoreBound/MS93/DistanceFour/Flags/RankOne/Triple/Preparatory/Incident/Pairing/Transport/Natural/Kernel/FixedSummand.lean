module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand.Action

/-!
# The incident local fixed summand

The binary S₃ calculation and its exact subgroup transport prove the two
required bounds conditionally on the concrete bar-action construction.
The first actual core acts trivially on the bar module. Constructing the
S₃ quotient marking and identifying the opposite-core displacement remain
separate obligations; no unconditional fixed-summand claim is made here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8)(3), printed p.906.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The actual bar action gives the fixed-summand calculation in the incident
configuration.  The first conclusion identifies the intrinsic fixed part of
the local span with the seed; the second lifts its full first-parabolic
fixation through the exact `Z_alpha` kernel. -/
theorem local_fixed_summand (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hd : flagIncident source i 1 d) :
    (flagFixedPreimage source i ⊓ Pairing.localSpan source i d ≤ Pairing.seed source i d) ∧
    ⁅flagFixedPreimage source i ⊓ Pairing.localSpan source i d,
      flagParabolic source i⁆ ≤ Z R (alpha R) := by
  let b := flagBarModule source geometry common.large_distance i hkernel
  obtain ⟨a⟩ := exists_barActionData source geometry common early i hkernel d hd
  exact local_fixed_summand_of_barAction b geometry common.large_distance hkernel d hd a

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
