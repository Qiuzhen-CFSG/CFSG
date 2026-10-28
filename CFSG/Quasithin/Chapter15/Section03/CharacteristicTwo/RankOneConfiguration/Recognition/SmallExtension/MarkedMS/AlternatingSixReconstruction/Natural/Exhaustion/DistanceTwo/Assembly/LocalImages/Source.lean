module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.Source

/-!
# Whole-core application of point-core image containment

The critical-image calculation now supplies both fields of LocalImageData
from containment of the literal replacement image in a conjugate point core.
The remaining plane and exponent inputs construct estimates for the actual
OrderedOrbit selected by Geometry.exists_orderedOrbit. Its recognized fixed
quotient excludes the non-Frattini branch. The Frattini branch and the two
literal embeddings then give the original whole-core equality.

This is conditional progress toward MS93 (3.6), printed pp.870--871. Image
containment, plane intersection and movement, and exponent two remain local
obligations of qt-e-ms-small-a6-exhaustion-distance-two. No conclusion about
a natural complement or the order of the whole cover is assumed.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
open Geometry Geometry.PairEstimates
universe u

/-- Actual exhaustion consumer, with only point-core containment on this
replacement. The three remaining source calculations are explicit and must
still be proved by the distance-two assembly owner. -/
theorem exhaustion_at_distance_two_of_point_core
    (hp : PlaneIntersectionInput.{u} KnownSimple.IsKnownSimple)
    (hm : PlaneMovementInput.{u} KnownSimple.IsKnownSimple)
    (he : PairedExponentInput.{u} KnownSimple.IsKnownSimple)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (t : Equiv.Perm (Fin 6))
    (hpoint : d.radical.map (Recognition.sourceProjection h e hz hn d) ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj t).toMonoidHom)
    (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R := by
  have hcentral := CentralLayer.replacement_centralLayer d e hz h
  by_cases hlarge : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)
  · exact exhaustion_of_graph_core_le h d (graph_core_le_of_frattini h d hcentral hlarge)
  have hi := LocalImages.localImageData_of_point_core h e hz hn d t hpoint hb hlarge
  have hP := replacement_radical_isPGroup h d
  have hQR := replacement_core_le_radical h d
  have hgen := replacement_residual_sup_radical h d
  have hs : LocalStructure (replacementGeometry h d) := {
    edge_centralizer := replacement_edge_centralizer h e hz d
    normal_generation := replacement_normal_generation h e hz d
    radical_derived := hi.radical_derived
    plane_eq := fun c b hc hab hcb =>
      replacement_plane_eq_of_intersection_bound h e hz d hb hlarge hc hab hcb
        (hp G L R h e hz hn d hcentral hb hlarge hi c b hc hab hcb)
    image_two := hi.image_two }
  have hl := localCalculations (replacementGeometry h d) hP hQR hgen hs hb hlarge
  obtain ⟨o⟩ := exists_orderedOrbit (replacementGeometry h d) hP hQR hl hb
  have hfull := source_images_full h e hz hn d hl hb hlarge hi.radical_derived o
  have estimates : PairEstimates d.radical o.c o.b o.opposite := {
    full_image := hfull.2
    moved_plane := hm G L R h e hz hn d hcentral hb hlarge hl hi o.c o.b
      o.critical o.adjacent_left o.adjacent_right hfull.2
    elementary_commutator :=
      (earlyPair hP hQR hl hb hlarge o).elementary_commutator_of_squares hP hQR hl
        (he hm G L R h e hz hn d hcentral hb hlarge hl hi o.c o.b o.opposite
          o.critical o.adjacent_left o.adjacent_right o.rebased o.strict_index
          o.ordered_index hfull.2 hfull.1) }
  let paired := pairedOrbit (replacementGeometry h d) hP hQR hgen hl hb hlarge o estimates
  exact (paired.false_of_recognized hP hQR
    (Recognition.orbitRecognition_knownSimple G L R h e hz hn d hcentral hb hlarge paired)).elim

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
