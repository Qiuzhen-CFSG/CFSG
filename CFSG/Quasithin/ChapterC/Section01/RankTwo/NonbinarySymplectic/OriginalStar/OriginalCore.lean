module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.PairedOrbit
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.Source
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Omega
public import Theory.Frattini.QuadraticCentralizer

/-!
# The original full core after a distance-two replacement

The distance-two theorem makes the original component short. Its intrinsic
layer is therefore the moved central omega subgroup of the full original
ambient two-core. The original omega-orbit comparison identifies this with
the original graph's U-layer. Central elementary displacement then places
the Frattini subgroup of every full original-color core in its full fixed
factor.

These are the original-core inputs from MS93 (3.6) used in the first
paragraph of (3.7), printed pp.870--872. The proof does not require the
replacement to contain the original ambient two-core, nor does it transfer
the replacement's critical distance or radical saturation to the original
graph. Original marked-star preservation remains a separate obligation.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A distance-two replacement controls the entire original graph core,
with the original radical and every central attachment retained. -/
theorem original_core_eq_U_of_distance_two_replacement
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex R} (ha : color R a = false) :
    core R a = U R a := by
  let := h.component_normal
  have hblock : IsBlock K :=
    ⟨inferInstance,(DistanceTwoRecognition.short_and_natural_of_distance_two h d g hb).1,
      h.component.subnormal⟩
  have hcore : core R (alpha R) = U R (alpha R) := by
    rw [graphCore_eq_intrinsic K R h.radical.isPGroup h.radical.twoCore_le h.residual_eq]
    change ((blockU K).map K.subtype).map (embedM R) = _
    rw [←BlockOmega.omega_commutator hblock,←h.initialCore_eq]
    rw [U,Z_alpha_eq_omegaOrbit,Ltilde_alpha,h.residual_eq,←map_commutator]
  obtain ⟨v,rfl⟩ := exists_mVertex_of_color R ha
  have hv : mVertex R v = act R v (alpha R) := by
    simp [alpha,act_mVertex]
  rw [hv,core_act,U_act,hcore]

/-- Source (3.6)'s Frattini fixedness holds on the full original core,
even though the supplied distance-two geometry belongs to its replacement. -/
theorem original_frattini_le_fixedCore_of_distance_two_replacement
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex R} (ha : color R a = false) :
    (frattini (Q R a)).map (Q R a).subtype ≤ fixedCore R a := by
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : IsElementaryAbelian 2 (U R a) := h.vertex_moving_elementary ha
  have hmove : ⁅Q R a,Ltilde R a⁆ ≤ U R a :=
    (original_core_eq_U_of_distance_two_replacement h d g hb ha).le
  have hc : U R a ≤ centralizer (Q R a : Set (FreeAmalgam R)) :=
    (DistanceEight.U_le_Z R a).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha))
  exact le_inf (map_subtype_le _)
    (frattini_image_le_centralizer_of_elementary_commutator
      (Q R a) (Ltilde R a) (U R a)
      (Q_isPGroup R h.radical.isPGroup h.radical.twoCore_le a ha)
      hmove (le_centralizer_iff.mp hc))

/-- The literal original-core premises used by the marked-star argument
on p.872, derived from the existing distance-two replacement theorem. -/
theorem original_core_source_of_distance_two_replacement
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex R} (ha : color R a = false) :
    ⁅Q R a,Ltilde R a⁆ = U R a ∧
      (frattini (Q R a)).map (Q R a).subtype ≤ fixedCore R a :=
  ⟨original_core_eq_U_of_distance_two_replacement h d g hb ha,
    original_frattini_le_fixedCore_of_distance_two_replacement h d g hb ha⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
