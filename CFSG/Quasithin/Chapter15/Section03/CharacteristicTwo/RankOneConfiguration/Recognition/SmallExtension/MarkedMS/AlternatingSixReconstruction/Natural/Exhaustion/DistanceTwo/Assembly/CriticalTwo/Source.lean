module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.Transposition.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.PointImage.Source

/-!
# Whole-core exhaustion with the critical-image premise discharged

The original non-Frattini configuration now supplies every order-two critical
image. The transposition sign calculation constructs the literal
LocalCalculations from the opposite-plane bound alone. Radical-derived
containment remains explicit for the subsequent full-edge-image estimate. The existing
recognition and whole-core application retain both original subgroup maps.

Radical-derived containment, plane intersection and paired exponent two
remain local obligations of qt-e-ms-small-a6-exhaustion-distance-two.
This conditional consumer does not complete MS93 (3.6), printed pp.870--871.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
open Geometry Geometry.PairEstimates
universe u

/-- The literal image interface now needs only its radical-derived field. -/
theorem localImageData_of_radical_derived
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup)
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    LocalImageData h d :=
  ⟨hder,fun _ hc => LocalImages.critical_image_two h e hz hn d hb hlarge hc⟩

/-- Apply the critical-image calculation to the actual replacement and
selected orbit, ending with the original whole commutator equality. -/
theorem exhaustion_at_distance_two_of_radical_derived
    (hp : PlaneIntersectionInput.{u} KnownSimple.IsKnownSimple)
    (he : PairedExponentInput.{u} KnownSimple.IsKnownSimple)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup)
    (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R := by
  have hcentral := CentralLayer.replacement_centralLayer d e hz h
  by_cases hlarge : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)
  · exact exhaustion_of_graph_core_le h d (graph_core_le_of_frattini h d hcentral hlarge)
  have hi := localImageData_of_radical_derived h e hz hn d hder hb hlarge
  have hl := localCalculations_of_intersection_bound h e hz hn d hb hlarge
    (hp G L R h e hz hn d hcentral hb hlarge hi)
  exact exhaustion_at_distance_two_of_local_calculations he h e hz hn d hl hder hb

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
