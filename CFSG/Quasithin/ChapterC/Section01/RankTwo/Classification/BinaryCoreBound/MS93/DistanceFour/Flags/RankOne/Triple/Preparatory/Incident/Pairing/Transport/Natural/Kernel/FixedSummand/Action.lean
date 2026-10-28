module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand.Action.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand.Action.Displacement

/-!
# The incident S₃ action on the actual bar module

The genuine rank-one quotient supplies the first full actor's projection,
and its exact two-core kernel permits descent of the literal bar action.
The opposite incident core has reflection image, giving the exact seed
image, while the two-residual supplies a cubic lift. This constructs every
field needed by the fixed-summand transport without additional geometric
or fixed-space assumptions.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8)(3), printed p.906,
using the intrinsic denominator of (1.7), printed pp.847--848.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Construct the S₃ action on the actual bar module, its tilded-residual
cubic lift, and the exact incident-seed reflection displacement. -/
theorem exists_barActionData (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hd : flagIncident source i 1 d) :
    Nonempty (BarActionData (flagBarModule source geometry common.large_distance i hkernel) d) := by
  let b := flagBarModule source geometry common.large_distance i hkernel
  obtain ⟨π, hπ, hk⟩ := exists_barProjection source i
  obtain ⟨ρ, ha⟩ := exists_descended_barRepresentation b geometry common early hkernel π hπ hk
  obtain ⟨t, ht, htn, himage⟩ := exists_incident_reflection source i d hd π hπ hk
  exact ⟨{
    projection := π
    representation := ρ
    action := ha
    cubic_lift := cubic_lift_of_surjective source i π hπ
    reflection := t
    reflection_square := ht
    reflection_ne_one := htn
    seed_image := seed_image_of_reflection b geometry common.large_distance hkernel d hd π ρ ha t himage
  }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
