module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Exponent.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.CriticalTwo.Source

/-!
# Whole-core exhaustion with paired exponent two discharged

The whole-cover calculation now supplies the actual paired exponent input.
Apply it with the proved plane movement to the orbit selected by the literal
relative-index ordering, and then to the original commutator exhaustion.
Only local images and the opposite-plane intersection remain explicit.
Their final discharge stays with qt-e-ms-small-a6-exhaustion-distance-two.
These conditional applications do not yet prove unconditional MS93 (3.6),
printed pp.870--871.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
open Geometry Geometry.PairEstimates
universe u

/-- The whole-cover square calculation removes the paired exponent premise
from all three literal orbit estimates. Local images remain an earlier input. -/
theorem pairEstimate_of_localImage
    (hi : LocalImageInput.{u} KnownSimple.IsKnownSimple) :
    PairEstimateInput.{u} KnownSimple.IsKnownSimple :=
  pairEstimate_of_inputs hi PlaneMovement.planeMovement_knownSimple pairedExponent_knownSimple

/-- Apply the completed paired square calculation to the actual ordered orbit,
with its reversed/rebased opposite and the source relative-index inequalities. -/
theorem exists_ordered_estimates_of_localImage
    (hi : LocalImageInput.{u} KnownSimple.IsKnownSimple)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hcentral : CentralLayer d) (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map (Q d.radical (alpha d.radical)).subtype ⊔
        X d.radical (alpha d.radical))
    (hl : LocalCalculations d.radical (replacementGeometry h d)) :
    ∃ o : OrderedOrbit (replacementGeometry h d), PairEstimates d.radical o.c o.b o.opposite :=
  exists_ordered_estimates hi PlaneMovement.planeMovement_knownSimple pairedExponent_knownSimple
    h e hz hn d hcentral hb hlarge hl

/-- Only the original image and plane-intersection obligations remain before
whole-core exhaustion. No exponent or natural-complement premise remains. -/
theorem distanceTwo_of_image_intersection
    (hi : LocalImageInput.{u} KnownSimple.IsKnownSimple)
    (hp : PlaneIntersectionInput.{u} KnownSimple.IsKnownSimple) :
    DistanceTwoInput.{u} KnownSimple.IsKnownSimple :=
  distanceTwo_of_image_intersection_exponent hi hp pairedExponent_knownSimple

/-- The literal whole-core consumer, retaining the original initialMoved
commutator and both replacement embeddings. -/
theorem exhaustion_at_distance_two_of_image_intersection
    (hi : LocalImageInput.{u} KnownSimple.IsKnownSimple)
    (hp : PlaneIntersectionInput.{u} KnownSimple.IsKnownSimple)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R :=
  exhaustion_of_graph_core_le h d (distanceTwo_of_image_intersection hi hp G L R h e hz hn d hb)

/-- Pointwise form discharging exponent two while keeping radical-derived
containment and the opposite-plane source calculation explicit. -/
theorem exhaustion_at_distance_two_of_radical_derived_and_intersection
    (hp : PlaneIntersectionInput.{u} KnownSimple.IsKnownSimple)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup)
    (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R :=
  exhaustion_at_distance_two_of_radical_derived hp pairedExponent_knownSimple h e hz hn d hder hb

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
