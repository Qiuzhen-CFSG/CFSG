module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Noncentral.Action
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.ResidualImages.Source
/-!
# Exhaustion of the cyclic-four residual image

The source orbit noncentrality and favorable-pair estimate construct an
actual elementary subgroup of order eight inside the literal radical
image. Every image of order at most eight is therefore elementary in the
contrary branch, and the proved elementary-image argument applies.
This exhausts the cyclic-four times central-transposition case.

The remaining alternative has image order sixteen and retains the Sylow
witness for the actual replacement radical. Its exhaustion and the final
distanceTwo_knownSimple assembly are still required. The applications here
use exhaustion_of_graph_core_le with the original quotient and inclusion.
Source: MS93 (3.6), printed p.871.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
open Geometry Geometry.BeforePlane
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R)

include h e hz hn in
/-- The favorable-pair calculation before plane equality supplies an actual
elementary subgroup of order eight in the original radical image. -/
theorem radical_image_contains_elementary_eight
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    ∃ A : Subgroup (Equiv.Perm (Fin 6)),
      A ≤ d.radical.map (Recognition.sourceProjection h e hz hn d) ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 8 := by
  have hp := replacement_radical_isPGroup h d
  have hQR := replacement_core_le_radical h d
  obtain ⟨o,hbase⟩ := exists_preliminaryPair_base (replacementGeometry h d) hp hQR
    (source_localData h e hz hn d hb hlarge) hb
  let s : ImageModel o := {
    projection := Recognition.sourceProjection h e hz hn d
    kernel := Recognition.sourceProjection_kernel h e hz hn d
    component_image := Recognition.sourceProjection_component h e hz hn d }
  let := o.quotient_elementary
  let := s.actor_elementary hp hQR
  let A := s.actor.map s.projection.range.subtype
  have hAelem : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAcard : Nat.card A = 8 := by
    rw [show Nat.card A = Nat.card s.actor from card_map_of_injective Subtype.coe_injective,
      s.actor_card hp hQR]
    exact (s.strict_indices hp hQR).1
  refine ⟨A,?_,hAelem,hAcard⟩
  rintro _ ⟨a,ha,rfl⟩
  obtain ⟨x,hx,rfl⟩ := ha
  have hxR : x ∈ d.radical := by
    have hxQ : embedM d.radical x ∈ Q d.radical o.b :=
      Q_le_adjacent_h d.radical (DistanceTwo.NaturalCore.edge_color o.adjacent_left)
        o.adjacent_right (o.opposite_le hx)
    rw [hbase,Q_beta] at hxQ
    obtain ⟨r,hr,he⟩ := hxQ
    exact embedM_injective d.radical he ▸ hr
  exact mem_map_of_mem (Recognition.sourceProjection h e hz hn d) hxR

include h e hz hn in
/-- Every proper radical image now gives the requested whole-core bound.
The source orbit noncentrality supplies the missing elementary-eight actor. -/
theorem graph_core_le_of_image_card_le_eight
    (hb : replacementDistance h d = 2)
    (h8 : Nat.card (d.radical.map (Recognition.sourceProjection h e hz hn d)) ≤ 8) :
    core d.radical (alpha d.radical) ≤ (replacementMoved d).map (embedM d.radical) := by
  by_cases hlarge : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)
  · exact graph_core_le_of_frattini h d (CentralLayer.replacement_centralLayer d e hz h) hlarge
  obtain ⟨A,hA,hAe,hAc⟩ := radical_image_contains_elementary_eight h e hz hn d hb hlarge
  have heq : A = d.radical.map (Recognition.sourceProjection h e hz hn d) :=
    eq_of_le_of_card_ge hA (h8.trans_eq hAc.symm)
  have hel : IsElementaryAbelian 2 (d.radical.map (Recognition.sourceProjection h e hz hn d)) :=
    heq ▸ hAe
  exact (false_of_elementary_image_nonfrattini h e hz hn d hel hb hlarge).elim

include h e hz hn in
/-- The cyclic-four residual case is exhausted on the original carriers. -/
theorem graph_core_le_of_cyclic_four_image
    (hb : replacementDistance h d = 2) (hfour : CyclicFourImage h e hz hn d) :
    core d.radical (alpha d.radical) ≤ (replacementMoved d).map (embedM d.radical) := by
  obtain ⟨a,t,ha,ht,hB,hdisj,hcomm,h8⟩ := hfour
  exact graph_core_le_of_image_card_le_eight h e hz hn d hb h8.le

include h e hz hn in
/-- Only the actual order-sixteen Sylow image remains in the whole-core
argument. No cyclic-four or local plane callback is retained. -/
theorem graph_core_le_or_sylow_image
    (hb : replacementDistance h d = 2) :
    core d.radical (alpha d.radical) ≤ (replacementMoved d).map (embedM d.radical) ∨
      (Nat.card (d.radical.map (Recognition.sourceProjection h e hz hn d)) = 16 ∧
        ∃ P : Sylow 2 d.overgroup, (P : Subgroup d.overgroup) = d.radical) := by
  rcases graph_core_le_or_residual_images h e hz hn d hb with hc | hfour | hsylow
  · exact Or.inl hc
  · exact Or.inl (graph_core_le_of_cyclic_four_image h e hz hn d hb hfour)
  · exact Or.inr hsylow

include h e hz hn in
/-- Apply the new cyclic-four branch to the literal original exhaustion. -/
theorem exhaustion_at_distance_two_of_cyclic_four_image
    (hb : replacementDistance h d = 2) (hfour : CyclicFourImage h e hz hn d) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R :=
  exhaustion_of_graph_core_le h d (graph_core_le_of_cyclic_four_image h e hz hn d hb hfour)

include h e hz hn in
/-- The exhaustion consumer retains only the original Sylow residual case. -/
theorem exhaustion_at_distance_two_or_sylow_image
    (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R ∨
      (Nat.card (d.radical.map (Recognition.sourceProjection h e hz hn d)) = 16 ∧
        ∃ P : Sylow 2 d.overgroup, (P : Subgroup d.overgroup) = d.radical) := by
  rcases graph_core_le_or_sylow_image h e hz hn d hb with hc | hr
  · exact Or.inl (exhaustion_of_graph_core_le h d hc)
  · exact Or.inr hr

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
