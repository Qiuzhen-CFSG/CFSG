module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.OmegaSeed
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour.KernelCentrality

/-!
# The two moving modules containing the G₂ critical triple

The proved G₂ source identity X = Z turns the midpoint central-omega
containment into containment in the actual midpoint seed. Its displacement
by the incident edge kernel lies in the midpoint moving subgroup, since
Z = U ⊔ edgeOmega. Combining this with the starting-edge calculation places
the literal critical triple in both moving modules, with the original
critical pair, first edge and midpoint unchanged.

These are the module identifications in the last paragraph of MS93 (3.8),
printed p.879. The auxiliary-subgroup contradiction and the resulting
NonfixedCriticalEdgeInput remain with qt-e-ms-small-g2-reconstruction.
Containment in these moving modules does not assert residual fixation.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour
open ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)
variable (h : SmallMSPair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
include h e

/-- At distance four, the entire derived radius lies in its original seed. -/
theorem radius_derived_le_seed
    (hb : (geometry h).b T = 4) (a : Vertex T) (ha : color T a = false) :
    ⁅V T a,V T a⁆ ≤ Z T a :=
  (radius_derived_le_omegaCenter h e hb a ha).trans_eq (omegaCenter_eq_seed h e a ha)

/-- The source X-layer has the same edge displacement bound as the seed. -/
theorem omegaCenter_edge_commutator_le_moving
    (a t : Vertex T) (ha : color T a = false) (hat : Adjacent T a t) :
    ⁅X T a,Q T t⁆ ≤ U T a := by
  rw [omegaCenter_eq_seed h e a ha]
  exact seed_edge_commutator_le_moving h a t ha hat

/-- The full critical commutator lies in the midpoint seed, with no central
kernel error and without assuming that the derived radius is fixed. -/
theorem critical_commutator_le_midpoint_seed
    (hb : (geometry h).b T = 4)
    (a z c : Vertex T) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    ⁅Z T a,Z T z⁆ ≤ Z T c :=
  (critical_commutator_le_midpoint_omegaCenter h e hb a z c hcColor hac hcz).trans_eq
    (omegaCenter_eq_seed h e c hcColor)

/-- The source triple belongs to the actual midpoint moving subgroup. -/
theorem critical_triple_le_midpoint_moving
    (hb : (geometry h).b T = 4)
    (a z t c : Vertex T) (hcColor : color T c = false)
    (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    ⁅⁅Z T a,Z T z⁆,Q T t⁆ ≤ U T c :=
  (commutator_mono
    (critical_commutator_le_midpoint_seed h e hb a z c hcColor hac hcz) le_rfl).trans
    (seed_edge_commutator_le_moving h c t hcColor hct)

/-- The two moving modules in the last paragraph of MS93 (3.8), on the
same original path and with the literal edge kernel as the third actor. -/
theorem critical_triple_le_moving_intersection
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hcColor : color T c = false)
    (hat : Adjacent T a t) (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    ⁅⁅Z T a,Z T z⁆,Q T t⁆ ≤ U T a ⊓ U T c :=
  le_inf (critical_triple_le_start_moving h a z ha hc t hat)
    (critical_triple_le_midpoint_moving h e hb a z t c hcColor hct hac hcz)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.DistanceFour
