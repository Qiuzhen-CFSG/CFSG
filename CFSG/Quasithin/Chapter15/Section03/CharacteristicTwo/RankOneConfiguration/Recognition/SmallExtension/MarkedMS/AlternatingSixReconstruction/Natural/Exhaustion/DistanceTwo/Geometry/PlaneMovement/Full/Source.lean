module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement.LowerBound
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Inputs

/-!
# Plane movement on the entire central cover

The maximal plane lies in the opposite-layer intersection, so its edge index
is at most four. The existing local commutator identity puts displacement in
that plane; the native lower bound then forces equality. This proves the exact
PlaneMovementInput and applies it to the literal selected OrderedOrbit.

The published contract explicitly retains LocalCalculations and LocalImageData.
Their construction and the paired exponent-two calculation remain obligations
of qt-e-ms-small-a6-exhaustion-distance-two. No further intersection, numerical,
point-marking, or natural-complement premise is used here.
Source: MS93 (3.6), printed p.871, the favorable-pair plane equality.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
open LargeDistance PairEstimates
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

include h e hz hn in
theorem plane_edge_bound_of_local_calculations
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c b : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl))
    (hab : Adjacent d.radical (alpha d.radical) b) (hcb : Adjacent d.radical c b) :
    (Z d.radical b).relIndex (criticalPlane d.radical c b) ≤ 4 := by
  have hc0 := critical_endpoint_color d.radical (alpha d.radical) rfl _ hc
  have hrev := critical_reverse_image_order_two h d hl hb hc
  have hedge := edge_layer_relIndex h e hz d hc0 hcb
  have h8 := native_edge_index_le_eight h e hz hn d hl hb hlarge
  let := finite_Z d.radical c
  have hPQ : criticalPlane d.radical c b ≤ Q d.radical (alpha d.radical) :=
    (replacement_plane_le_intersection h e hz d hb hlarge hc hab hcb).trans inf_le_right
  have hmid : 2 ≤ (criticalPlane d.radical c b).relIndex (Z d.radical c) := by
    rw [←hrev]
    exact relIndex_le_of_le_left hPQ (index_ne_zero_of_finite (H :=
      (criticalPlane d.radical c b).subgroupOf (Z d.radical c)))
  have hmul := relIndex_mul_relIndex (Z d.radical b) (criticalPlane d.radical c b)
    (Z d.radical c) (edge_Z_le_criticalPlane (replacementGeometry h d) hc hab hcb)
    (criticalPlane_le_opposite c b)
  rw [hedge] at hmul
  nlinarith

include h e hz hn in
theorem plane_eq_displacement_of_local_calculations
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    (hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup)
    {c b : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl))
    (hab : Adjacent d.radical (alpha d.radical) b) (hcb : Adjacent d.radical c b)
    (himage : criticalOrbit d.radical c b ⊔ Q d.radical c = Q d.radical b) :
    ⁅criticalOrbit d.radical c b,Z d.radical c⁆ ⊔ Z d.radical b =
      criticalPlane d.radical c b := by
  let A := criticalOrbit d.radical c b
  let D := ⁅A,Z d.radical c⁆ ⊔ Z d.radical b
  have hc0 := critical_endpoint_color d.radical (alpha d.radical) rfl _ hc
  have hAR : A ≤ Q d.radical b := le_sup_left.trans_eq himage
  have hAnZ : A ≤ normalizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    (hAR.trans (fun _ hx => hx.2 c (adjacent_symm d.radical hcb))).trans
      (Z_normalized d.radical c)
  have hZAn : Z d.radical c ≤ normalizer (A : Set (FreeAmalgam d.radical)) :=
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
      (by change 0 < replacementDistance h d; omega) hc).trans
      (criticalOrbit_normalized c b)
  have hDP : D ≤ criticalPlane d.radical c b := by
    apply sup_le _ (edge_Z_le_criticalPlane (replacementGeometry h d) hc hab hcb)
    apply le_criticalPlane_of_commutator_le _
      (le_normalizer_iff_commutator_le_right.mp hAnZ)
    exact (commutator_mono le_rfl
      (le_normalizer_iff_commutator_le_left.mp hZAn)).trans
        (hl.commutator_edge c b hc hab hcb)
  have hfour : 4 ≤ (Z d.radical b).relIndex D := by
    dsimp only [D]
    rw [orbit_displacement h e hz d hc0 hcb himage,
      edge_displacement_relIndex h e hz d hc0 hcb]
    exact native_displacement_index_ge_four h e hz hn d hl hb hlarge hder
  have hbound := plane_edge_bound_of_local_calculations h e hz hn d hl hb hlarge hc hab hcb
  have hmul := relIndex_mul_relIndex (Z d.radical b) D
    (criticalPlane d.radical c b) le_sup_right hDP
  let := finite_Z d.radical c
  let : Finite (criticalPlane d.radical c b) :=
    Finite.of_injective (inclusion (criticalPlane_le_opposite c b)) (inclusion_injective _)
  have hpos : 0 < D.relIndex (criticalPlane d.radical c b) :=
    Nat.pos_of_ne_zero (index_ne_zero_of_finite
      (H := D.subgroupOf (criticalPlane d.radical c b)))
  have hone : D.relIndex (criticalPlane d.radical c b) = 1 := by nlinarith
  exact le_antisymm hDP (relIndex_eq_one.mp hone)

theorem planeMovement_knownSimple : PlaneMovementInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h e hz hn d _ hb hlarge hl hi c b hc hab hcb himage
  exact plane_movement h d hb hc
    (plane_eq_displacement_of_local_calculations h e hz hn d hl hb hlarge
      hi.radical_derived hc hab hcb himage) hab

include h e hz hn in
theorem exists_orderedOrbit_with_full_movement_of_local_calculations
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    (hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup) :
    ∃ o : OrderedOrbit (replacementGeometry h d),
      criticalPlane d.radical o.c o.b ≤
        ⁅criticalOrbit d.radical o.c o.b,stabilizer d.radical (alpha d.radical)⁆ ⊔
          Z d.radical (alpha d.radical) ∧
      criticalOrbitNative d.radical o.c o.b =
        ⁅pResidual 2 d.overgroup,criticalOrbitNative d.radical o.c o.b⁆ ⊔
          orbitLayer d.radical := by
  obtain ⟨o⟩ := exists_orderedOrbit (replacementGeometry h d)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d) hl hb
  have himage := (source_images_full h e hz hn d hl hb hlarge hder o).2
  have heq := plane_eq_displacement_of_local_calculations h e hz hn d hl hb hlarge hder
    o.critical o.adjacent_left o.adjacent_right himage
  have hmove := plane_movement h d hb o.critical heq o.adjacent_left
  refine ⟨o,hmove,?_⟩
  exact full_movement_of_plane (replacementGeometry h d) (pResidual 2 d.overgroup)
    (replacement_radical_isPGroup h d) (replacement_residual_sup_radical h d)
    hb o.critical o.adjacent_left o.adjacent_right
    (hl.orbit_core _ _ o.critical o.adjacent_left o.adjacent_right) hmove

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
