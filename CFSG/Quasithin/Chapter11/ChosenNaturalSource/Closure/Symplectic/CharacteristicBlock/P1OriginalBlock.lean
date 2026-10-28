module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.MSRecognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison.OriginalBlock

/-!
# Original closure block from the distance-two source endgame

Apply original-component recognition to the literal MS product L O₂(G₁).
The subgroup equivalence returns the block on L with its whole intrinsic
conjugation module. No Frattini-smallness premise on the original product
is needed: the distance-two theorem proves the requisite intrinsic core
control in its characteristic replacement.

The SourceEndgame witness and actual distance-two geometry remain genuine
source premises. Source: MS93 (3.6)--(3.7), printed pp.870--877, and
Aschbacher--Smith C.1.32 and 11.5.7.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.Chapter12.Section02
open ChapterC.BinaryMS.MS93
open ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open ChapterC.RankTwo.NonbinarySymplectic
open ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)

/-- The literal closure component is a block once its distance-two endgame
is supplied, with no separate whole ambient Frattini bound. -/
theorem msPair_sp4FourBlock_of_distance_two_source_endgame
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)))
    (g : ChapterC.BinaryMS.MS93.Geometry d.radical) (hb : g.b d.radical = 2)
    {z t : Vertex d.radical}
    (path : CriticalPath d.radical g (alpha d.radical) z)
    (hat : Adjacent d.radical (alpha d.radical) t)
    (hzt : Adjacent d.radical z t)
    (c : EdgeMarking (intrinsicMSInput E m hms) d (alpha d.radical) t)
    (c' : EdgeMarking (intrinsicMSInput E m hms) d z t)
    (u : Sp E.input.field.Carrier)
    (s : SourceEndgame (intrinsicMSInput E m hms) d (z := z) c u) :
    ChapterC.IsSp4FourBlock L := by
  have hb := s.original_block path hb hat hzt c'
  let e : L.subgroupOf (L ⊔ E.G₁.pCoreIn 2) ≃* L := subgroupOfEquivOfLe le_sup_left
  obtain ⟨hs,F,hF,hfinite,hcard,rho,⟨model⟩,haction⟩ := hb
  exact ⟨hs.of_mulEquiv e,F,hF,hfinite,hcard,rho,⟨model.comap e.symm⟩,haction⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
