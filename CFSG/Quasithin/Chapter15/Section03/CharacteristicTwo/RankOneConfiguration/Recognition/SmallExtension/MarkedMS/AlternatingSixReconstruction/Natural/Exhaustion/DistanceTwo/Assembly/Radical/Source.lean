module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.Radical.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.Exponent.Source

/-!
# Exhaustion outside the full Sylow image

The actual radical has a central transposition in its six-letter image.
Every image smaller than order sixteen therefore supplies both LocalImageData
clauses. Apply these to the selected orbit and whole-core consumer using the
proved paired exponent and plane movement. Only the opposite-plane estimate
remains explicit in this branch. The exceptional order-sixteen image gives a
Sylow subgroup on the original replacement carrier, not a substituted radical.

The Sylow and plane obligations remain with
qt-e-ms-small-a6-exhaustion-distance-two; these reductions do not complete
MS93 (3.6), printed pp.870--871.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
open Geometry Geometry.LocalImages
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R)

/-- Apply the small-image derived containment to the original whole-core
exhaustion. The plane input remains a source obligation of this task. -/
theorem exhaustion_at_distance_two_of_image_card_ne_sixteen
    (hp : PlaneIntersectionInput.{u} KnownSimple.IsKnownSimple)
    (hb : replacementDistance h d = 2)
    (h16 : Nat.card (d.radical.map (Recognition.sourceProjection h e hz hn d)) ≠ 16) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R := by
  by_cases hlarge : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)
  · exact exhaustion_of_graph_core_le h d (graph_core_le_of_frattini h d
      (CentralLayer.replacement_centralLayer d e hz h) hlarge)
  exact exhaustion_at_distance_two_of_radical_derived_and_intersection hp h e hz hn d
    (radical_derived_of_image_card_ne_sixteen h e hz hn d hb hlarge h16) hb

/-- Once the plane estimate is supplied, failure of the literal exhaustion
forces the replacement radical itself to be Sylow, with quotient order sixteen.
This isolates the remaining radical branch without assuming it away. -/
theorem exhaustion_or_sylow_radical
    (hp : PlaneIntersectionInput.{u} KnownSimple.IsKnownSimple)
    (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R ∨
      (Nat.card (d.radical.map (Recognition.sourceProjection h e hz hn d)) = 16 ∧
        ∃ P : Sylow 2 d.overgroup, (P : Subgroup d.overgroup) = d.radical) := by
  by_cases hlarge : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)
  · exact Or.inl (exhaustion_of_graph_core_le h d (graph_core_le_of_frattini h d
      (CentralLayer.replacement_centralLayer d e hz h) hlarge))
  rcases radical_derived_or_image_sixteen h e hz hn d hb hlarge with hder | h16
  · exact Or.inl (exhaustion_at_distance_two_of_radical_derived_and_intersection
      hp h e hz hn d hder hb)
  · exact Or.inr ⟨h16,radical_sylow_of_image_sixteen h e hz hn d hb hlarge h16⟩

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
