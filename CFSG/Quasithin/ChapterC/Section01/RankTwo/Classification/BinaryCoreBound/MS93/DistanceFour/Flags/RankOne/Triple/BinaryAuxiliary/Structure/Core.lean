module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Reductions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross

/-!
# The p.907 core calculation from the moving quotient

The source naturality calculation constructs the marked natural coordinates
on X/Z_alpha from the moving quotient. The midpoint comparison then gives
both full-actor cross-commutator bounds, and full-actor transitivity gives
the fixed-preimage decomposition at every incident first flag. These results
construct all fields of CoreCalculation from the original preparatory data
and the explicit MovingFactor input.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The decomposition field is derived from the full second commutator bound;
natural coordinates and both commutator bounds remain explicit premises. -/
theorem coreCalculation_of_natural_and_commutators
    (source : LocalSource L R) (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (i : Bool) (natural : FlagNaturalSection source i) (d : M)
    (n : XFactor source i d)
    (hfirst : ∀ g : M, flagIncident source i g d →
      ⁅⁅X source i d, localFlagKernel source i g⁆, localFlagActor source i g⁆ ≤ Z R (alpha R))
    (hsecond : ⁅secondFlagLayer source i d, localFlagActor source (!i) d⁆ ≤ X source i d) :
    Nonempty (CoreCalculation source i d) := by
  exact ⟨⟨n, hfirst, hsecond,
    second_decomposition_of_commutator source geometry hlarge i natural d hsecond⟩⟩

/-- The source X calculation and all cross-layer identities on p.907.
The moving quotient is an explicit input; the natural X coordinates and
both full-actor commutator bounds are constructed from the source data. -/
theorem coreCalculation
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i)
    (moving : MovingFactor source i p.delta0) :
    Nonempty (CoreCalculation source i p.delta0) := by
  obtain ⟨x⟩ := coreNaturality source geometry common hb early i hkernel natural p moving
  obtain ⟨hfirst, hsecond⟩ :=
    coreCrossCommutators source geometry common hb early i hkernel natural p moving x
  exact coreCalculation_of_natural_and_commutators source geometry (by omega)
    i natural p.delta0 x hfirst hsecond

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
