module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.P1FieldFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison.SelectedNatural

/-!
# Field four from an action-selected replacement marking

The replacement cover chooses its own symplectic marking while preserving
the literal MS groups, reduction and degree. The selected natural-coordinate
theorem fills the natural fields of SourceEndgame using that same marking.
The remaining root, point, index and movement hypotheses below are all stated
in the selected coordinates. The degree conclusion returns to the original
closure field; no compatibility with its former abstract group marking is
assumed. This does not discharge the remaining geometric hypotheses.

Source: MS93 (3.7), printed pp.876–877; Aschbacher–Smith 11.5.7.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.SpecificGroups.SymplecticFour
open Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.Chapter12.Section02
open ChapterB.QuasisimpleSource
open ChapterC.BinaryMS.MS93
open ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open ChapterC.RankTwo.NonbinarySymplectic
open ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison
open ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison.Selected
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (C : Geometry D) (m : MarkedFlag C)

theorem msPair_field_card_eq_four_of_selected_geometry
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      C.input.field L (C.G₁.pCoreIn 2))
    (d : CharacteristicReduction (L.subgroupOf (L ⊔ C.G₁.pCoreIn 2))
      ((C.G₁.pCoreIn 2).subgroupOf (L ⊔ C.G₁.pCoreIn 2)))
    {g : ChapterC.BinaryMS.MS93.Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking (selectedInput (intrinsicMSInput C m hms) d) d a t)
    (c' : EdgeMarking (selectedInput (intrinsicMSInput C m hms) d) d z t) (u : Sp (select (intrinsicMSInput C m hms) d).field.Carrier)
    (hwhole : Q d.radical a = U d.radical a ⊔ fixedCore d.radical a)
    (hroot : (layerImage d a (Z d.radical z)).map (markedQuotient (selectedInput (intrinsicMSInput C m hms) d) d c u) =
      RootSubgroup.group 0)
    (hopposite : (stabilizer (point (select (intrinsicMSInput C m hms) d).field.Carrier)).comap (markedQuotient (selectedInput (intrinsicMSInput C m hms) d) d c u) ≤
      normalizer (layerImage d a (Z d.radical z) : Set (FixedQuotient d a)))
    (hintersection : (layerImage d a (Z d.radical z)).relIndex (layerImage d a (Z d.radical a)) = 2^C.input.field.degree)
    (hintercentral : layerImage d a (Z d.radical a) ⊓ layerImage d a (Z d.radical z) ≤
      relativeCentralizer (selectedInput (intrinsicMSInput C m hms) d) d (z := z) c u)
    (hcentralorder : (layerImage d a (Z d.radical a) ⊓ layerImage d a (Z d.radical z)).relIndex
      (relativeCentralizer (selectedInput (intrinsicMSInput C m hms) d) d (z := z) c u) = 2^C.input.field.degree)
    (hcentralnorm : (stabilizer (point (select (intrinsicMSInput C m hms) d).field.Carrier)).comap (markedQuotient (selectedInput (intrinsicMSInput C m hms) d) d c u) ≤
      normalizer (relativeCentralizer (selectedInput (intrinsicMSInput C m hms) d) d (z := z) c u : Set (FixedQuotient d a)))
    (hprojection : (layerImage d a (Z d.radical a)).relIndex
      (relativeCentralizer (selectedInput (intrinsicMSInput C m hms) d) d (z := z) c u ⊔ layerImage d a (Z d.radical a)) = 2^C.input.field.degree)
    (hdisjoint : Disjoint (fixedCore d.radical a) (U d.radical z))
    (hcommutator : Nat.card (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) = 2^C.input.field.degree)
    (hstrict : 2^C.input.field.degree < Nat.card (⁅Z d.radical z,markedPointCore (selectedInput (intrinsicMSInput C m hms) d) d c u ⊓
      Q d.radical t⁆ : Subgroup (FreeAmalgam d.radical))) : Nat.card C.input.field.Carrier = 4 := by
  let s := select (intrinsicMSInput C m hms) d
  exact (degree_and_original_field_of_geometry (intrinsicMSInput C m hms) d s.field s.degree s.equiv s.cover
    path hb hat hzt c c' u hwhole hroot hopposite hintersection hintercentral hcentralorder
    hcentralnorm hprojection hdisjoint hcommutator hstrict).2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
