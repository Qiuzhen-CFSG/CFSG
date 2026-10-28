module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.Decomposition

/-!
# Elementary structure of the original commutator-core center

The reverse-center calculation puts the entire center of the replacement
commutator core in its elementary Z-layer. The characteristic replacement
preserves the commutator core itself, so its literal isomorphism transports
elementarity to the original ambient core. The fixed factor is retained;
neither its order nor its original ambient centrality is asserted.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5)(iv) and section 7,
printed pp.895--900 and 932--933.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}}
  {L R : Subgroup J} {h : Input κ L R} (t : InputSetup h)

/-- The complete center of the original core is elementary, including its
possibly larger component-fixed kernel. -/
theorem original_core_center_elementary
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    IsElementaryAbelian 2 (center (commutatorCore L)) := by
  let := DistanceEight.CoreFactors.Center.core_center_elementary common earlier
  exact IsElementaryAbelian.of_surjective (centerCongr t.coreEquiv).toMonoidHom
    (centerCongr t.coreEquiv).surjective

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
