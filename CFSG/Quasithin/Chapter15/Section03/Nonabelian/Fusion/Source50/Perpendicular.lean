module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.NonabelianBranch
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.OrthogonalMarks

/-!
# The literal perpendicular for the terminal orthogonal marking

The finite movement calculation uses the entire Sylow fixed line. That
line is the actual Z and has order two; its unique nonidentity element
therefore suffices to test perpendicularity. Both the determinant and
standard orthogonal conventions retain the same binary polar form.

Source: Aschbacher–Smith, 15.3.53(2) and 15.3.60, printed pp.1146,1150.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open OrthogonalGeometry
attribute [local instance] FourGroupMatrixCoordinates.naturalAction orthogonalAction
variable {G : Type*} [Group G] [Finite G]
variable (d : CharacteristicTwo.LocalData G) (H : Subgroup G)
  (h : (localSetup d H).Hypothesis)
include h

theorem intersection_perpendicular
    (hf : ∀ g : G, d.V.map (MulAut.conj g).toMonoidHom ≤ d.M →
      d.V.map (MulAut.conj g).toMonoidHom ≤ centralizer (d.V : Set G))
    (hnon : ¬ IsMulCommutative (localSpan d.V H))
    (hu : ¬ IsMulCommutative (localSpan d.ZS H))
    (z : d.V) (hz : orderOf (z : G) = 2) (hmark : zpowers (z : G) = d.Z)
    (x : d.V) :
    (x : G) ∈ localSpan d.ZS H ↔
      OrthogonalFourBinary.form.polarBilin
        ((FusionCore.OriginalCoordinates.standardAction d.action).coordinates z).toAdd
        ((FusionCore.OriginalCoordinates.standardAction d.action).coordinates x).toAdd = 0 := by
  let := span_image_elementary d H h
  let P := d.action.sylowImage d.T d.sylow_le
  let R := d.action.image (localSpan d.ZS H)
  have him := intersection_coordinates_movement d H h hf hnon hu
  have hcoord : d.action.coordinates x ∈ OrthogonalGeometry.Source50Model.movement R ↔
      (x : G) ∈ localSpan d.ZS H := by
    rw [← him]
    change d.action.coordinates.toMonoidHom x ∈ _ ↔ _
    rw [mem_map_iff_mem (f := d.action.coordinates.toMonoidHom) d.action.coordinates.injective]
    exact ⟨fun h => h.2,fun h => ⟨x.property,h⟩⟩
  have hzfix : d.Z = (fixedVectors P).map d.action.vectorEmbedding := by
    change centralInvolutions d.T = _
    rw [NaturalOrthogonalAction.centralInvolutions_eq_fixedPlane d.T d.sylow_le d.action,
      d.action.fixedPlane_eq_map d.sylow_le]
    rw [show (P : Subgroup OrthogonalActor) = d.action.image (d.T : Subgroup G) from
      d.action.coe_sylowImage d.T d.sylow_le]
  have hzmem : d.action.coordinates z ∈ fixedVectors P := by
    have hm : (z : G) ∈ d.Z := hmark ▸ mem_zpowers (z : G)
    rw [hzfix] at hm
    have he : d.action.vectorEmbedding (d.action.coordinates z) = (z : G) := by
      simp [NaturalOrthogonalAction.vectorEmbedding]
    rw [← he,mem_map_iff_mem d.action.vectorEmbedding_injective] at hm
    exact hm
  have hz1 : d.action.coordinates z ≠ 1 := by
    intro he
    have hze : z=1 := d.action.coordinates.injective (he.trans (map_one _).symm)
    have hg : (z : G)=1 := congrArg Subtype.val hze
    simp [hg] at hz
  have hall : ∀ w ∈ fixedVectors P, w=1 ∨ w=d.action.coordinates z := by
    obtain ⟨a,_,ha⟩ := (Nat.card_eq_two_iff' (1 : fixedVectors P)).mp
      (OrthogonalGeometry.sylow_fixedVectors_card P)
    intro w hw
    by_cases he : w=1
    · exact Or.inl he
    · right
      exact congrArg (fun a : fixedVectors P => (a : OrthogonalVector))
        ((ha ⟨w,hw⟩ (fun e=>he (congrArg Subtype.val e))).trans
          (ha ⟨d.action.coordinates z,hzmem⟩ (fun e=>hz1 (congrArg Subtype.val e))).symm)
  have hout : ¬ R ≤ OrthogonalGeometry.Source50Model.planePart P := by
    have he : d.action.image d.S=OrthogonalGeometry.Source50Model.planePart P := by
      rw [d.action.image_planeStabilizer,OrthogonalGeometry.setwise_plane_eq_ker]
      rfl
    rw [← he]
    exact nonabelian_image_outside_stabilizer d H h hu
  rw [← hcoord,OrthogonalGeometry.Source50Model.movement_mem_iff_perpendicular P R
    (span_image_le_sylow d H h) (sylow_normalizes_span_image d H h) hout]
  have hp : OrthogonalGeometry.Source50Model.polarValue (d.action.coordinates x)
      (d.action.coordinates z) = OrthogonalFourBinary.form.polarBilin
        ((FusionCore.OriginalCoordinates.standardAction d.action).coordinates z).toAdd
        ((FusionCore.OriginalCoordinates.standardAction d.action).coordinates x).toAdd := by
    rw [standard_polar_eq_coordinateValue]
    dsimp only [OrthogonalGeometry.Source50Model.polarValue]
    rw [mul_comm]
    ring
  constructor
  · intro hw
    rw [← hp]
    exact hw _ hzmem
  · intro hx w hw
    rcases hall w hw with rfl | rfl
    · simp [OrthogonalGeometry.Source50Model.polarValue,FusionCore.orthogonalCoordinateValue,
        OrthogonalFourBinary.form]
    · exact hp.trans hx

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
