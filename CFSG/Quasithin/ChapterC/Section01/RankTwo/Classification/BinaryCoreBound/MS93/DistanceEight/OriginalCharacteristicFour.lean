module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.OriginalCentralFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.ThirdCommutator

/-!
# The intrinsic identity of the original distance-eight four-group

The source subgroup H is the third lower-central subgroup of the actual
commutator core. Both original inclusions preserve commutators, and the
characteristic replacement preserves that core. Thus the original four-group
has an intrinsic description independent of the replacement choice.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5), printed pp.895--900,
and its characteristic replacement on pp.932--933.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}}
  {L T : Subgroup J} {h : Input κ L T} (t : InputSetup h)
/-- The source four is intrinsically the third lower-central subgroup of the original core. -/
theorem reducedCentralFour_eq_third_commutator
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    t.reducedCentralFour = ⁅⁅commutatorCore L, commutatorCore L⁆, commutatorCore L⁆ := by
  rw [reducedCentralFour, ← DistanceEight.CoreFactors.Center.core_third_commutator_eq_H common earlier,
    core_alpha _ t.source.two_group t.source.core_le t.source.residual,
    ← map_commutator, ← map_commutator,
    comap_map_eq_self_of_injective (embedM_injective _),
    map_commutator, map_commutator, t.reduction.commutatorCore_eq h]
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
