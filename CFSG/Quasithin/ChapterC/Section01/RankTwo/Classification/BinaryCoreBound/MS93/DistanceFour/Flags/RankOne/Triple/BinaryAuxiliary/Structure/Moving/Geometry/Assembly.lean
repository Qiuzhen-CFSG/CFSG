module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.Residual

/-!
# Assembly of the midpoint comparison data

The midpoint Sylow selection and the reverse index comparison provide the
transported actor, core escape and commutator estimate.  The core-action and
residual arguments provide the two original-flag action fields.  Together they
construct the exact `MiddleComparisonData` required by the moving quotient.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The source midpoint comparison and both action estimates at its incident flag. -/
theorem middleComparisonData
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i) :
    Nonempty (MiddleComparisonData source geometry i p (middleTransport p)) := by
  obtain ⟨e, he, hactor, hescape, hcomparison⟩ :=
    exists_reverse_middle_comparison source geometry common hb early i hkernel natural p
  refine ⟨{
    flag := e
    incident := he
    actor := hactor
    escapes := hescape
    comparison := hcomparison
    core := ?_
    residual := ?_ }⟩
  · exact Y_core_le_second source geometry common early i hkernel e
  · exact Y_residual_not_le_second source geometry common hb early i hkernel natural p e

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
