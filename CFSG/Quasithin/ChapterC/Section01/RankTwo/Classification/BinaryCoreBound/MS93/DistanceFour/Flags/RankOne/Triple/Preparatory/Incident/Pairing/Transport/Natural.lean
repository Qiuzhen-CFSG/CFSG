module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel

/-!
# Natural-section calculations at the incident pairing

The basic calculations establish the unquotiented moving containment, the
seed's fixed-preimage bound, and the nonzero opposite fixed space. Here the
surjective natural coordinates on the actual local span are combined with
the exact intrinsic-kernel comparison to construct the remaining factor.
Only the kernel field changes: the SL₂ epimorphism, coordinates and literal
conjugation equation are those descended through the quotient by D_alpha.
The tilded residual defining the flag denominator remains distinct from
the full local actor acting on this factor.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8)(3), printed p.906,
applying (1.7)(i), pp.847--848.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The incident local span is a genuine natural rank-one factor with the
global component-fixed preimage as its exact intrinsic denominator. -/
theorem rankOneFactor_nonempty (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i) (d : M) (hd : flagIncident source i 1 d)
    (htriple : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R)) :
    let E := Quotient.extension source (representative source i d hd)
    let P := RankOnePairing.localParabolic E i
    Nonempty (RankOnePairing.RankOneFactor (RankOnePairing.localResidual P)
      (RankOnePairing.localGenerated P (Quotient.seed source i d))
      (Quotient.fixed source i d hd)) := by
  obtain ⟨n⟩ := Coordinates.rankOneFactor_nonempty source geometry common.large_distance
    i hkernel natural d hd
  exact ⟨{ n with
    kernel := n.kernel.trans
      (Kernel.sectionKernel_subgroupOf_eq source geometry common early i hkernel d hd htriple) }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural
