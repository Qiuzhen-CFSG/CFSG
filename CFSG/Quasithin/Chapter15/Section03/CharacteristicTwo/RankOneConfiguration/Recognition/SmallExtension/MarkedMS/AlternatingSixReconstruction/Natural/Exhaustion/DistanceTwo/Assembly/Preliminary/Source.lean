module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.Noncentral.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Exponent.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Vertex.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Recognition.Source
/-!
# Terminal exhaustion from the preliminary pair's plane calculations

The preliminary orbit has an elementary paired commutator and the faithful
fixed quotient. Plane movement gives full component movement, and the
three-subgroups argument makes the literal fixed kernel central. Thus the
involution argument applies without a full radical-image hypothesis.

Both plane premises below remain source obligations. The whole-core consumer
uses the original replacement maps; these theorems do not yet assert the
unconditional distance-two result. Source: MS93 (3.6), printed p.871.
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
/-- The source terminal argument needs movement of the plane, but does not
need the favorable orbit image to fill the whole radical image. -/
theorem false_of_preliminary_plane_calculations
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    (o : PreliminaryPair d.radical (replacementGeometry h d))
    (hplane : criticalPlane d.radical o.c o.b ≤
      ⁅criticalOrbit d.radical o.c o.b,stabilizer d.radical (alpha d.radical)⁆ ⊔
        Z d.radical (alpha d.radical))
    (hmove : ⁅criticalOrbit d.radical o.c o.b,criticalPlane d.radical o.c o.b⁆ ≠ ⊥) :
    False := by
  have hp := replacement_radical_isPGroup h d
  have hQR := replacement_core_le_radical h d
  have hm := full_movement_of_plane (replacementGeometry h d) (pResidual 2 d.overgroup)
    hp (replacement_residual_sup_radical h d) hb o.critical o.adjacent_left o.adjacent_right
    o.orbit_le_core hplane
  have hc := fixedKernel_central_of_full_movement (pResidual 2 d.overgroup) hp hQR
    o.orbit_le_core
    (orbit_commutator_centralizes_residual_of_transposition h e hz hn d hb hlarge
      o.critical o.adjacent_left o.adjacent_right) hm
  let s : ImageModel o := {
    projection := Recognition.sourceProjection h e hz hn d
    kernel := Recognition.sourceProjection_kernel h e hz hn d
    component_image := Recognition.sourceProjection_component h e hz hn d }
  exact o.false_of_recognized hp hQR
    (Exponent.paired_commutator_elementary h e hz hn d hb hlarge o) hc hmove
    (s.recognized_of_full_movement (h.sqtk.subgroup d.overgroup) hp hQR hm)

include h e hz hn in
/-- Literal whole-core consumer of the reduced terminal argument. The two
plane calculations are still explicit mathematical obligations. -/
theorem exhaustion_of_preliminary_plane_calculations
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    (o : PreliminaryPair d.radical (replacementGeometry h d))
    (hplane : criticalPlane d.radical o.c o.b ≤
      ⁅criticalOrbit d.radical o.c o.b,stabilizer d.radical (alpha d.radical)⁆ ⊔
        Z d.radical (alpha d.radical))
    (hmove : ⁅criticalOrbit d.radical o.c o.b,criticalPlane d.radical o.c o.b⁆ ≠ ⊥) :
    ⁅pCore 2 (L ⊔ R : Subgroup G),L.subgroupOf (L ⊔ R)⁆ = initialMoved L R :=
  exhaustion_of_graph_core_le h d
    (false_of_preliminary_plane_calculations h e hz hn d hb hlarge o hplane hmove).elim

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
