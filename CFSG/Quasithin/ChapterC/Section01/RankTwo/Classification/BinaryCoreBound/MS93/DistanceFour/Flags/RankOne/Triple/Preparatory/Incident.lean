module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Coverage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Locality

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.SourceData
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.FixedSpaces
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Displacement

/-!
# The source incident package for MS93 (4.6.8)

The completed finite pairing application gives delta2 and claim (3).
The three-neighbor fixed-space calculation selects delta0 with the printed
first-actor bound and middle noncontainment. Finally, the actual endpoint
action on the second layer proves claim (4) by the binary Y contradiction.
Together these construct `SourceFlagLocalData` from the original conditional
inputs, preserving the quotient marking and original amalgam embedding.

The corrected selection uses the first full actor and target Z_alpha.
The legacy `FlagLocalData` record and its conditional interfaces are unchanged.
The authorized propagation premise remains in the assembly interface, although
the stronger binary displacement argument does not require it.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), printed pp.905--906, especially claims (3)--(4) on p.906.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The corrected source incident package. Every incident choice, triple,
selection bound and displacement conclusion is constructed from the original
inputs; propagation is the explicitly authorized conditional interface. -/
theorem sourceFlagLocalData (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i) (p : FlagCriticalData source geometry i)
    (_propagation : FlagPropagation p) : Nonempty (SourceFlagLocalData p) := by
  obtain ⟨d₂, hd₂, hcross, htriple⟩ :=
    exists_delta2_triple source geometry common hb early i hkernel natural p
  obtain ⟨d₀, hd₀, hnot, hcomm, hmiddle⟩ :=
    Incident.exists_source_delta0 source geometry common hb early i hkernel natural p
  exact ⟨{
    delta2 := d₂
    delta2_neighbor := hd₂
    endpoint_crosses := hcross
    second_triple := htriple
    delta0 := d₀
    delta0_neighbor := hd₀
    endpoint_not_le := hnot
    intersection_commutator := hcomm
    middle_not_le := hmiddle
    displacement := Incident.displacement_of_selection source geometry common hb early i
      hkernel natural p d₀ hd₀ hnot hmiddle
  }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
