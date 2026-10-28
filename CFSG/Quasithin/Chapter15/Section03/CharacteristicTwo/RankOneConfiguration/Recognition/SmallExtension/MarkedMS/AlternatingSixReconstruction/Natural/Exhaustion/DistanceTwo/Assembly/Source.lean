module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.CentralLayer.Edges
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition.Source

/-!
# Distance-two assembly with the proved central layer and recognition

The original replacement now supplies its entire moving layer, and the actual
paired-orbit fixed quotient has been recognized. Only four local source
calculations remain: the radical and critical images, the opposite-plane
intersection, plane movement, and exponent two for the paired commutator.

These are explicit obligations of the distance-two exhaustion owner. Neither
the recovered exponent-four bound nor the conditional assembly below
discharges them. The last theorem applies the graph containment through the
literal subgroup inclusions to the original whole commutator.
Source: MS93 (3.3), (3.6), pp.866--871; Section 7, pp.932--933.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
universe u
open Geometry Geometry.PairEstimates

/-- Central-layer construction and recognition are discharged on the original
carriers. The remaining paired-orbit geometry stays explicit. -/
theorem distanceTwo_of_geometry
    (hg : OrbitGeometryInput.{u} KnownSimple.IsKnownSimple) :
    DistanceTwoInput.{u} KnownSimple.IsKnownSimple :=
  distanceTwo_of_inputs centralLayer_knownSimple hg Recognition.orbitRecognition_knownSimple

/-- Assemble the four remaining local calculations, all owned by the
distance-two theorem, with no central-layer or recognition callback. -/
theorem distanceTwo_of_local_inputs
    (hi : LocalImageInput.{u} KnownSimple.IsKnownSimple)
    (hp : PlaneIntersectionInput.{u} KnownSimple.IsKnownSimple)
    (hm : PlaneMovementInput.{u} KnownSimple.IsKnownSimple)
    (he : PairedExponentInput.{u} KnownSimple.IsKnownSimple) :
    DistanceTwoInput.{u} KnownSimple.IsKnownSimple :=
  distanceTwo_of_geometry (orbitGeometry_of_calculations
    (localCalculationInput_of_source_inputs hi hp) (pairEstimate_of_inputs hi hm he))

/-- The literal whole-core exhaustion consumer; distance two remains the
authorized hypothesis discharged by the independent large-distance branch. -/
theorem exhaustion_at_distance_two_of_local_inputs
    (hi : LocalImageInput.{u} KnownSimple.IsKnownSimple)
    (hp : PlaneIntersectionInput.{u} KnownSimple.IsKnownSimple)
    (hm : PlaneMovementInput.{u} KnownSimple.IsKnownSimple)
    (he : PairedExponentInput.{u} KnownSimple.IsKnownSimple)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : replacementDistance h d = 2) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R :=
  exhaustion_of_graph_core_le h d
    (distanceTwo_of_local_inputs hi hp hm he G L R h e hz hn d hb)

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

