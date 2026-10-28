module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.Inputs
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Plane.Source

/-!
# Whole-core exhaustion at distance two

The Frattini branch follows from the basis theorem. In the other branch,
choose the favorable critical pair before imposing plane equality. Its
order-eight point-core image gives the plane displacement and noncentrality
on the whole natural or augmentation cover. Recognition of the literal
orbit fixed quotient then forces that orbit to be elementary, contradicting
its plane movement. This includes the order-sixteen radical-image case.

The final application pulls the containment through the original replacement
and subgroup embeddings. Distance two is the only remaining conditional
hypothesis; its independent producer belongs to the large-distance argument.
Source: MS93 (3.6), printed pp.870--871, and Section 7, pp.932--933;
Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
open Geometry.BeforePlane
universe u

/-- The complete distance-two branch, retaining the entire moved cover and
without local-image, plane-intersection or paired-orbit premises. -/
theorem distanceTwo_knownSimple : DistanceTwoInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h e hz hn d hb
  by_cases hsmall : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)
  · exact graph_core_le_of_frattini h d
      (CentralLayer.replacement_centralLayer d e hz h) hsmall
  obtain ⟨o,_⟩ := exists_preliminaryPair_base (replacementGeometry h d)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
    (source_localData h e hz hn d hb hsmall) hb
  exact (false_of_preliminary_nonfrattini h e hz hn d o hb hsmall).elim

/-- Whole-core exhaustion on the original group and its literal moved layer. -/
theorem exhaustion_at_distance_two_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R :=
  exhaustion_of_graph_core_le h d (distanceTwo_knownSimple G L R h e hz hn d hb)

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
