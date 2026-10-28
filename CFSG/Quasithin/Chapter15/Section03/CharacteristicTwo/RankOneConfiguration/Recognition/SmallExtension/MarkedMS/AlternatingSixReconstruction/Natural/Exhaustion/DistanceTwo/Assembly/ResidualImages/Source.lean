module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.Radical.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.Intersection.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.Radical.NonElementary
/-!
# Two residual images in whole-core exhaustion

The critical transposition is central in the literal replacement radical
image. Apply the finite-image calculation to identify every proper
non-elementary image by commuting, disjoint cyclic generators of orders
four and two. The other non-elementary case has image order sixteen and
makes the original replacement radical itself a Sylow subgroup.

The elementary-image branch already exhausts the entire moved cover,
including its central attachment. Apply that result and the literal graph
pullback to obtain an exhaustion alternative for the original commutator.
Neither residual alternative is excluded here: the distance-two source
argument and final assembly remain with this task's owner.

Source context: MS93 (3.3), (3.6), printed pp.866--871.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
open Geometry Geometry.LocalImages
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R)

/-- This residual alternative records generators and their literal image,
not a group-family label. The central transposition is retained. -/
def CyclicFourImage : Prop :=
  ∃ a t : Equiv.Perm (Fin 6),
    orderOf a = 4 ∧ t.IsSwap ∧
    d.radical.map (Recognition.sourceProjection h e hz hn d) = zpowers a ⊔ zpowers t ∧
    Disjoint (zpowers a) (zpowers t) ∧ Commute a t ∧
    Nat.card (d.radical.map (Recognition.sourceProjection h e hz hn d)) = 8

include h e hz hn in
/-- The actual radical image in the unresolved source branch is elementary,
a literal cyclic-four times transposition product, or a full Sylow image. -/
theorem radical_image_three_cases
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    IsElementaryAbelian 2 (d.radical.map (Recognition.sourceProjection h e hz hn d)) ∨
      CyclicFourImage h e hz hn d ∨
      Nat.card (d.radical.map (Recognition.sourceProjection h e hz hn d)) = 16 := by
  classical
  by_cases he : IsElementaryAbelian 2 (d.radical.map (Recognition.sourceProjection h e hz hn d))
  · exact Or.inl he
  by_cases h16 : Nat.card (d.radical.map (Recognition.sourceProjection h e hz hn d)) = 16
  · exact Or.inr (Or.inr h16)
  obtain ⟨t,ht,htB,hcent⟩ := radical_image_central_transposition h e hz hn d hb hlarge
  obtain ⟨a,_,ha,hB,hdisj,hcomm,h8⟩ := cyclic_four_times_swap_of_non_elementary _
    ((replacement_radical_isPGroup h d).map _) h16 t ht htB hcent he
  exact Or.inr (Or.inl ⟨a,t,ha,ht,hB,hdisj,hcomm,h8⟩)

include h e hz hn in
/-- Whole-core containment is established except for these two precise
non-elementary images. In the order-sixteen case the original radical itself
is Sylow; it is not replaced by an unrelated Sylow subgroup. -/
theorem graph_core_le_or_residual_images
    (hb : replacementDistance h d = 2) :
    core d.radical (alpha d.radical) ≤ (replacementMoved d).map (embedM d.radical) ∨
      CyclicFourImage h e hz hn d ∨
      (Nat.card (d.radical.map (Recognition.sourceProjection h e hz hn d)) = 16 ∧
        ∃ P : Sylow 2 d.overgroup, (P : Subgroup d.overgroup) = d.radical) := by
  classical
  by_cases hlarge : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)
  · exact Or.inl (graph_core_le_of_frattini h d
      (CentralLayer.replacement_centralLayer d e hz h) hlarge)
  rcases radical_image_three_cases h e hz hn d hb hlarge with hel | hfour | hsylow
  · exact Or.inl (graph_core_le_of_elementary_image h e hz hn d hel hb)
  · exact Or.inr (Or.inl hfour)
  · exact Or.inr (Or.inr ⟨hsylow,radical_sylow_of_image_sixteen h e hz hn d hb hlarge hsylow⟩)

include h e hz hn in
/-- Literal classification consumer of the residual-image reduction. Both
remaining alternatives keep the original quotient and subgroup inclusion. -/
theorem exhaustion_at_distance_two_or_residual_images
    (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R ∨
      CyclicFourImage h e hz hn d ∨
      (Nat.card (d.radical.map (Recognition.sourceProjection h e hz hn d)) = 16 ∧
        ∃ P : Sylow 2 d.overgroup, (P : Subgroup d.overgroup) = d.radical) := by
  rcases graph_core_le_or_residual_images h e hz hn d hb with hc | hr
  · exact Or.inl (exhaustion_of_graph_core_le h d hc)
  · exact Or.inr hr
end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
