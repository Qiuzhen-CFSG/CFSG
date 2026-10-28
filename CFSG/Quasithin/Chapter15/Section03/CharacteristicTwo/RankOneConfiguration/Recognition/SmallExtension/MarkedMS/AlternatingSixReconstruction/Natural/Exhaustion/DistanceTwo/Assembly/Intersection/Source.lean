module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Intersection.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.Exponent.Source

/-!
# Whole-core exhaustion for the elementary radical-image branch

The whole-cover intersection calculation now constructs every local orbit
identity. Elementary image also supplies radical-derived containment, so the
proved plane movement and paired exponent calculations apply to the literal
selected orbit. Recognition rules out the non-Frattini branch. The Frattini
branch then identifies the whole core with its original moved layer.

The last applications use exhaustion_of_graph_core_le on the unchanged
replacement. A bound on every radical square is a sufficient remaining local
premise; it is not asserted as a source hypothesis. Its construction, or an
alternative elimination of the non-elementary images, remains with
qt-e-ms-small-a6-exhaustion-distance-two. These conditional results do not
establish distanceTwo_knownSimple. Source: MS93 (3.6), pp.870--871, and
Section 7, pp.932--933.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
open Geometry Geometry.PairEstimates Geometry.Intersection
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R)

include h e hz hn in
/-- The elementary image branch cannot occur in the original non-Frattini
configuration: construct the plane, local calculations and actual paired orbit,
then apply its recognized fixed quotient. -/
theorem false_of_elementary_image_nonfrattini
    (hel : IsElementaryAbelian 2 (d.radical.map (Recognition.sourceProjection h e hz hn d)))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) : False := by
  let := hel
  have hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup := by
    rw [←Recognition.sourceProjection_kernel h e hz hn d]
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator]
    exact commutator_self_eq_bot_iff.mpr hel.toIsMulCommutative
  have hl := localCalculations_of_elementary_image h e hz hn d hel hb hlarge
  have hcentral := CentralLayer.replacement_centralLayer d e hz h
  have hi := localImageData_of_radical_derived h e hz hn d hder hb hlarge
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
        (pairedExponent_knownSimple PlaneMovement.planeMovement_knownSimple G L R h e hz hn d
          hcentral hb hlarge hl hi o.c o.b o.opposite o.critical o.adjacent_left o.adjacent_right
          o.rebased o.strict_index o.ordered_index hfull.2 hfull.1) }
  let paired := pairedOrbit (replacementGeometry h d) hP hQR
    (replacement_residual_sup_radical h d) hl hb hlarge o estimates
  exact paired.false_of_recognized hP hQR
    (Recognition.orbitRecognition_knownSimple G L R h e hz hn d hcentral hb hlarge paired)

include h e hz hn in
/-- The exact graph-core target for an elementary literal radical image.
No plane-intersection, local-calculation, or paired-orbit callback remains. -/
theorem graph_core_le_of_elementary_image
    (hel : IsElementaryAbelian 2 (d.radical.map (Recognition.sourceProjection h e hz hn d)))
    (hb : replacementDistance h d = 2) :
    core d.radical (alpha d.radical) ≤ (replacementMoved d).map (embedM d.radical) := by
  by_cases hlarge : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)
  · exact graph_core_le_of_frattini h d (CentralLayer.replacement_centralLayer d e hz h) hlarge
  exact (false_of_elementary_image_nonfrattini h e hz hn d hel hb hlarge).elim

include h e hz hn in
/-- The original exhaustion consumer of the whole-cover intersection proof,
retaining both original replacement inclusions and the full moved layer. -/
theorem exhaustion_at_distance_two_of_elementary_image
    (hel : IsElementaryAbelian 2 (d.radical.map (Recognition.sourceProjection h e hz hn d)))
    (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R :=
  exhaustion_of_graph_core_le h d (graph_core_le_of_elementary_image h e hz hn d hel hb)

include h e hz hn in
/-- A square bound on the original radical is a sufficient remaining local
condition. It is not assumed of the radical in the source theorem. -/
theorem graph_core_le_of_radical_squares
    (hsq : ∀ r ∈ d.radical, r ^ 2 ∈ pCore 2 d.overgroup)
    (hb : replacementDistance h d = 2) :
    core d.radical (alpha d.radical) ≤ (replacementMoved d).map (embedM d.radical) := by
  let q := Recognition.sourceProjection h e hz hn d
  let B := d.radical.map q
  have hpow : ∀ x : B, x ^ 2 = 1 := by
    intro x
    obtain ⟨r,hr,he⟩ := x.property
    apply Subtype.ext
    change x.val ^ 2 = 1
    rw [←he,←map_pow]
    have hh : r ^ 2 ∈ q.ker := by
      rw [Recognition.sourceProjection_kernel]
      exact hsq r hr
    exact hh
  have hcomm : IsMulCommutative B := ⟨⟨fun a b =>
    Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hpow x)) a b⟩⟩
  let : IsElementaryAbelian 2 B := {
    toIsMulCommutative := hcomm
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  exact graph_core_le_of_elementary_image h e hz hn d inferInstance hb

include h e hz hn in
/-- Apply the square reduction to the unchanged whole-core exhaustion. -/
theorem exhaustion_at_distance_two_of_radical_squares
    (hsq : ∀ r ∈ d.radical, r ^ 2 ∈ pCore 2 d.overgroup)
    (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R :=
  exhaustion_of_graph_core_le h d (graph_core_le_of_radical_squares h e hz hn d hsq hb)

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
