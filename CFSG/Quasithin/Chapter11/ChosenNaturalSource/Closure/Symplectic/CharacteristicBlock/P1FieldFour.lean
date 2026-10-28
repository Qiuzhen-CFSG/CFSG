module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.MSRecognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison

/-!
# The conditional field-four consumer for the literal closure input

The point-parabolic comparison is formulated on the literal saturated
distance-two layers and retains the original `Sp₄` quotient marking.  This
module only transports its already proved conditional conclusion to the
closure input.  The `SourceEndgame` witness remains an explicit source
obligation; in particular, this file does not replace it by an abstract
replacement-component action.
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

/- The field conclusion is stated with the literal original field carrier,
   rather than with the auxiliary field occurring in a replacement cover. -/
theorem msPair_field_card_eq_four_of_source_endgame
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
    Nat.card E.input.field.Carrier = 4 := by
  exact s.field_card_eq_four path hb hat hzt c'

theorem msPair_field_degree_eq_two_of_source_endgame
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
    E.input.field.degree = 2 := by
  exact s.degree_eq_two path hb hat hzt c'

/-- The conditional block consumer after the original Frattini bound has been
proved.  The source witness and the Frattini bound are intentionally separate
premises: they come from different source branches. -/
theorem msPair_sp4FourBlock_of_source_endgame
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
    (s : SourceEndgame (intrinsicMSInput E m hms) d (z := z) c u)
    (hsmall : ⁅pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G),
        L.subgroupOf (L ⊔ E.G₁.pCoreIn 2)⁆ ≤
      (frattini (pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G))).map
        (pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G)).subtype ⊔
      omegaCenterIn (pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G))) :
    ChapterC.IsSp4FourBlock L := by
  apply sp4FourBlock_of_field_four_frattini_small E m hms
    (msPair_field_card_eq_four_of_source_endgame E m hms d g hb path hat hzt c c' u s)
    hsmall

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
