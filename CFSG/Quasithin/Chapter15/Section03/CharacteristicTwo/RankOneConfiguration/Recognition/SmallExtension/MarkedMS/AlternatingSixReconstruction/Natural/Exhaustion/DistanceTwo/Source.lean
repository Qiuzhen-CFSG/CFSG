module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Inputs

/-!
# Assembly of the alternating-six distance-two reconstruction

The Frattini branch uses Burnside's basis theorem on the actual finite
replacement. In the other branch the selected paired orbit, its canonical
fixed quotient, and the kernel displacement give the terminal involution
contradiction. Both branches retain the entire initial moved layer.

The three source inputs remain unproved here. This is conditional assembly,
not an unconditional proof of DistanceTwoInput for the known-simple catalogue.
The final theorem applies the graph conclusion through both literal inclusions
to exhaust the original component commutator.

Source: MS93 (3.6), printed pp.870--871; Section 7, pp.932--933.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
universe u

/-- Discharge both branches once the independent source constructions are proved. -/
theorem distanceTwo_of_inputs {κ : GroupClass.{u}}
    (hc : CentralLayerInput κ) (hg : OrbitGeometryInput κ)
    (hr : OrbitRecognitionInput κ) : DistanceTwoInput κ := by
  intro G _ _ L R h e hz hn d hb
  have hl := hc G L R h e hz hn d
  by_cases hs : core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)
  · exact graph_core_le_of_frattini h d hl hs
  · obtain ⟨o⟩ := hg G L R h e hz hn d hl hb hs
    exact (o.false_of_recognized (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d) (hr G L R h e hz hn d hl hb hs o)).elim

/-- Actual consumer: the conclusion identifies the original whole commutator,
with the same restriction and free-amalgam embeddings as Exhaustion.Setup. -/
theorem exhaustion_at_distance_two {κ : GroupClass.{u}}
    (hc : CentralLayerInput κ) (hg : OrbitGeometryInput κ) (hr : OrbitRecognitionInput κ)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G), L.subgroupOf (L ⊔ R)⁆ = initialMoved L R :=
  exhaustion_of_graph_core_le h d (distanceTwo_of_inputs hc hg hr G L R h e hz hn d hb)

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
