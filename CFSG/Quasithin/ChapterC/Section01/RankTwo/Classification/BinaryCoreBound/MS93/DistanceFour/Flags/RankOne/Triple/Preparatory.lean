module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.SourceData
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident

/-!
# Preparatory geometry for MS93 (4.6.8)

`flagCriticalData` constructs the critical endpoint and noncentral midpoint
through beta from the contrary triple hypothesis. The layer results prove
representative independence and identify the actual quotient fixed preimages.

`sourceFlagPreparatoryData` assembles that critical configuration, the proved
propagation argument (2), and the incident-flag arguments (3)--(4). Every
field of `SourceFlagPreparatoryData` is constructed, including the printed
delta0 bound with the first full parabolic and target Z_alpha. The natural
section remains the explicitly supplied hypothesis; no intermediate
configuration, propagation or incident conclusion is assumed.

The legacy records retain their separate conditional interfaces. The binary
auxiliary-layer argument on pp.907--908 and final `FlagControl` assembly
belong to the consuming `Triple` development.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), printed pp.905--906.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The complete source preparatory package on p.906 of (4.6.8), conditional
only on the original local facts, selected kernel, contrary triple and natural
section. The critical configuration and claims (2)--(4) are all constructed. -/
theorem sourceFlagPreparatoryData (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (natural : FlagNaturalSection source i) :
    Nonempty (SourceFlagPreparatoryData source geometry i) := by
  obtain ⟨p⟩ := flagCriticalData source geometry common hb i hbad
  have propagation := flagPropagation source geometry common hb early i hkernel natural p
  obtain ⟨d⟩ := sourceFlagLocalData source geometry common hb early i hkernel natural p
    propagation
  exact ⟨{
    middle := p.middle
    endpoint := p.endpoint
    critical := p.critical
    middle_neighbor := p.middle_neighbor
    first_distance := p.first_distance
    second_distance := p.second_distance
    middle_triple := p.middle_triple
    delta2 := d.delta2
    delta2_neighbor := d.delta2_neighbor
    endpoint_crosses := d.endpoint_crosses
    propagation := propagation
    second_triple := d.second_triple
    delta0 := d.delta0
    delta0_neighbor := d.delta0_neighbor
    endpoint_not_le := d.endpoint_not_le
    intersection_commutator := d.intersection_commutator
    middle_not_le := d.middle_not_le
    displacement := d.displacement
  }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
