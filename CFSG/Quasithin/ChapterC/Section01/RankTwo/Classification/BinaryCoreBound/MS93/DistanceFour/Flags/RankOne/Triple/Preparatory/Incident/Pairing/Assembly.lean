module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Coverage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Locality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Assembly

/-!
# The incident triple in MS93 (4.6.8)(3)

Select delta2 by the critical endpoint's crossing of an incident opposite
core. If its barred triple vanished, `Transport` constructs the genuine
finite marked pairing source in G_alpha/D_alpha and applies (1.7)(i).
Its moving containment and fixed-core commutator bound contradict the
critical midpoint's noncentral triple via `contradiction_of_pairing`.

Both premises of the earlier conditional selection are discharged here
from the original natural section and critical data. The last actor remains
the tilded incident residual; the full untilded actor is used only in the
finite pairing application. No propagation or delta0 selection is required.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.7)(i), printed pp.847--848, and (4.6.8)(3), printed p.906.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The incident delta2 selection and original MS93 (4.6.8), claim (3).
The finite application of (1.7)(i) is constructed from the natural section,
with no additional pairing or later flag hypotheses. -/
theorem exists_delta2_triple (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i) (p : FlagCriticalData source geometry i) :
    ∃ d : M, flagIncident source i 1 d ∧
      ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) ∧
      ¬ ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
        localFlagResidual source (!i) d⁆ ≤ Z R (alpha R) :=
  Incident.Pairing.exists_delta2_triple_of_pairing source geometry common hb early i hkernel p
    (Incident.Pairing.Transport.moving_premise source geometry common i hkernel p)
    (Incident.Pairing.Transport.pairing_premise source geometry common early i hkernel natural p)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
