module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Index
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement

/-!
# Naturality of the binary auxiliary core quotient

The source index calculation bounds the literal X/Z_alpha by four, and
the incident pencil proves nonzero residual movement. The existing
recognition theorem consequently constructs its natural coordinates,
surjective full-actor map, exact local-core kernel and ambient conjugation
equation from the original preparatory configuration and moving factor.
No dimension assertion about the whole Y/U quotient is needed.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The source natural X factor on p.907, with the full local actor and
both exact kernels, after discharging the size and residual-movement bounds. -/
theorem coreNaturality
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i)
    (moving : MovingFactor source i p.delta0) :
    Nonempty (XFactor source i p.delta0) := by
  exact coreNaturality_of_index_and_movement source geometry common early i p.delta0 moving
    (core_index_le_four source geometry common hb early i hkernel natural p moving)
    (X_residual_commutator_not_le source geometry common hb early i hkernel natural p moving)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
