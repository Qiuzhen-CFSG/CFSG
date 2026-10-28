module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement.Full.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.LocalImages.Source

/-!
# Whole-core exhaustion after recognition of the radical image

The actual radical image is constructed as a conjugate point core from the
local calculations and its abelian quotient. This discharges the point-core
containment premise in the literal exhaustion consumer, including both
embeddings back to the original commutator. The central attachment is retained.

The earlier local calculations, radical-derived containment, plane intersection
and paired exponent two remain explicit obligations of
qt-e-ms-small-a6-exhaustion-distance-two. This is a conditional assembly, not
an unconditional proof of MS93 (3.6), printed pp.870--871.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
open Geometry Geometry.PairEstimates
universe u

theorem exhaustion_at_distance_two_of_local_calculations
    (he : PairedExponentInput.{u} KnownSimple.IsKnownSimple)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R)
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup)
    (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R := by
  by_cases hlarge : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)
  · exact exhaustion_of_graph_core_le h d (graph_core_le_of_frattini h d
      (CentralLayer.replacement_centralLayer d e hz h) hlarge)
  obtain ⟨t,ht⟩ := PlaneMovement.radical_image_point_core h e hz hn d hl hb hlarge hder
  have hcentral := CentralLayer.replacement_centralLayer d e hz h
  have hi := LocalImages.localImageData_of_point_core h e hz hn d t ht.le hb hlarge
  have hP := replacement_radical_isPGroup h d
  have hQR := replacement_core_le_radical h d
  obtain ⟨o⟩ := exists_orderedOrbit (replacementGeometry h d) hP hQR hl hb
  have hfull := source_images_full h e hz hn d hl hb hlarge hder o
  have estimates : PairEstimates d.radical o.c o.b o.opposite := {
    full_image := hfull.2
    moved_plane := PlaneMovement.planeMovement_knownSimple G L R h e hz hn d
      hcentral hb hlarge hl hi o.c o.b o.critical o.adjacent_left o.adjacent_right hfull.2
    elementary_commutator :=
      (earlyPair hP hQR hl hb hlarge o).elementary_commutator_of_squares hP hQR hl
        (he PlaneMovement.planeMovement_knownSimple G L R h e hz hn d hcentral hb
          hlarge hl hi o.c o.b o.opposite o.critical o.adjacent_left o.adjacent_right
          o.rebased o.strict_index o.ordered_index hfull.2 hfull.1) }
  let paired := pairedOrbit (replacementGeometry h d) hP hQR
    (replacement_residual_sup_radical h d) hl hb hlarge o estimates
  exact (paired.false_of_recognized hP hQR
    (Recognition.orbitRecognition_knownSimple G L R h e hz hn d hcentral hb hlarge paired)).elim

/-- Plane movement is now discharged in the exact graph-core target. The
three remaining inputs are local obligations of this same assembly owner. -/
theorem distanceTwo_of_image_intersection_exponent
    (hi : LocalImageInput.{u} KnownSimple.IsKnownSimple)
    (hp : PlaneIntersectionInput.{u} KnownSimple.IsKnownSimple)
    (he : PairedExponentInput.{u} KnownSimple.IsKnownSimple) :
    DistanceTwoInput.{u} KnownSimple.IsKnownSimple :=
  distanceTwo_of_local_inputs hi hp PlaneMovement.planeMovement_knownSimple he

/-- Apply the improved graph-core assembly through the literal replacement
and original subgroup embeddings. -/
theorem exhaustion_at_distance_two_of_image_intersection_exponent
    (hi : LocalImageInput.{u} KnownSimple.IsKnownSimple)
    (hp : PlaneIntersectionInput.{u} KnownSimple.IsKnownSimple)
    (he : PairedExponentInput.{u} KnownSimple.IsKnownSimple)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R :=
  exhaustion_of_graph_core_le h d
    (distanceTwo_of_image_intersection_exponent hi hp he G L R h e hz hn d hb)

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
