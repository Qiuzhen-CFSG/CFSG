module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.SaturatedMSRecognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoFixedCore

/-!
# The fixed-core quadraticity step on the original closure MS-pair

The literal closure quotient and its original symplectic input satisfy the
fixed-core contradiction in MS93 (3.7)(2). The entire opposite fixed core
moves at most q squared cosets on U and acts quadratically on the full Z-layer.
The full central covering kernel and both fixed attachments are retained.

This discharges the fixed-core quadraticity step, not the later whole-core
index estimates or field restriction. Source: Meierfrankenfeld--Stellmacher
(1993), printed p.873; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open ChapterC.BinaryMS.MS93 ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open ChapterC.RankTwo.NonbinarySymplectic
open CFSG.Quasithin.Chapter12.Section02
open SaturatedDistanceTwo
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)
include m

/-- The original closure marking satisfies the full fixed-core quadraticity
conclusion of the large-movement contradiction, with no added index premise. -/
theorem msPair_saturated_source_two_fixedCore
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t) :
    (centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) ≤ Nat.card E.input.field.Carrier^2 ∧
      ⁅⁅Z d.radical z,fixedCore d.radical a⁆,fixedCore d.radical a⁆ = ⊥ := by
  let h := intrinsicMSInput E m hms
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  refine ⟨?_,source_two_fixedCore_quadratic h d g hb hsat path hat hzt c c'⟩
  simpa only [E.input.field.card_eq] using
    source_two_fixedCore_movement_le_square h d g hb hsat path hat hzt c c'

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
