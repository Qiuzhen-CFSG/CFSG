module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Inputs
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition.Image
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition.Projection

/-!
# Source recognition of the distance-two fixed quotient

The initial natural central quotient supplies the actual six-letter marking.
The paired orbit makes its opposite actor quadratic on the literal orbit
quotient, and hence elementary. The strict index inequality excludes an
alternating-only image, giving the full symmetric action. Natural quotient
recognition and the augmentation-cover calculation then give transitivity
and displacement for the canonical fixed-space preimage, retaining its
possible central line. The terminal theorem applies both conclusions to
`PairedOrbit.false_of_recognized` on the same replacement and orbit.

Source: MS93 (3.6), printed p.871, and Section 7, pp.932--933.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition
universe u

/-- Every original natural replacement has this actual six-letter marking;
surjectivity and actor elementary structure are proved separately from its orbit. -/
def sourceImageModel {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    {L R : Subgroup G} (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R)
    (o : PairedOrbit (pResidual 2 d.overgroup) d.radical (replacementGeometry h d)) :
    ImageModel o where
  projection := sourceProjection h e hz hn d
  kernel := sourceProjection_kernel h e hz hn d
  component_image := sourceProjection_component h e hz hn d

/-- Both recognition clauses under the original source hypotheses and the
independently supplied actual paired orbit. No action-model premise remains. -/
theorem orbitRecognition_knownSimple : OrbitRecognitionInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h e hz hn d _ _ _ o
  let := o.quotient_elementary
  let s := (sourceImageModel h e hz hn d o).permutationModel
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
  exact s.recognized (h.sqtk.subgroup d.overgroup)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)

/-- The actual terminal consumer, on the literal quotient and fixed kernel
of the selected paired orbit. Geometry and the central layer stay explicit. -/
theorem false_of_source_pair {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hl : CentralLayer d) (hd : replacementDistance h d = 2)
    (hf : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    (o : PairedOrbit (pResidual 2 d.overgroup) d.radical (replacementGeometry h d)) : False :=
  o.false_of_recognized (replacement_radical_isPGroup h d)
    (replacement_core_le_radical h d)
    (orbitRecognition_knownSimple G L R h e hz hn d hl hd hf o)

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
