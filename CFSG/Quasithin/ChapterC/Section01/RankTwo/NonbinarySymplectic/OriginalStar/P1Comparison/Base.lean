module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoPointDisplacement
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.SubgroupTransport

/-!
# The full fixed quotient on the original star

The tilde groups in MS93 (3.7), pp.876--877, are images inside the
original endpoint stabilizer modulo its complete component-fixed core.
The quotient below retains this entire kernel. A supplied endpoint marking
and one inner conjugation descend together, so the natural and opposite
sections can use the same symplectic coordinates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
open Theory.SpecificGroups.SymplecticFour
variable {H : Type*} [Group H] (R : Subgroup H)

/-- The entire fixed attachment, viewed in its own endpoint stabilizer. -/
@[expose] def fixedAttachment (a : Vertex R) : Subgroup (stabilizer R a) :=
  (fixedCore R a).subgroupOf (stabilizer R a)

instance fixedAttachment_normal (a : Vertex R) : (fixedAttachment R a).Normal :=
  normal_subgroupOf_of_le_normalizer (DistanceEight.PathCentrality.fixedCore_normalized R a)

/-- The original source tilde quotient. -/
@[expose] def FixedQuotient (a : Vertex R) := stabilizer R a ⧸ fixedAttachment R a

instance fixedQuotientGroup (a : Vertex R) : Group (FixedQuotient R a) :=
  inferInstanceAs (Group (stabilizer R a ⧸ fixedAttachment R a))

/-- Projection through the complete fixed attachment. -/
@[expose] def fixedProjection (a : Vertex R) : stabilizer R a →* FixedQuotient R a :=
  QuotientGroup.mk' (fixedAttachment R a)

/-- Restrict an ambient layer to the endpoint and take its actual tilde image. -/
@[expose] def layerImage (a : Vertex R) (B : Subgroup (FreeAmalgam R)) :
    Subgroup (FixedQuotient R a) :=
  (B.subgroupOf (stabilizer R a)).map (fixedProjection R a)

variable {F : Type*} [Field F] {a : Vertex R}
variable (κ : stabilizer R a →* Sp F)
variable (hκ : κ.ker = (Q R a).subgroupOf (stabilizer R a))

include hκ in
private theorem fixedAttachment_le_kernel (u : Sp F) :
    fixedAttachment R a ≤ ((MulAut.conj u).toMonoidHom.comp κ).ker := by
  intro x hx
  have hxQ : x ∈ κ.ker := hκ.symm ▸ (show x.val ∈ Q R a from hx.1)
  change u * κ x * u⁻¹ = 1
  rw [show κ x = 1 from hxQ]
  simp

/-- The chosen endpoint quotient descends using the same inner conjugation. -/
def markedQuotient (u : Sp F) : FixedQuotient R a →* Sp F :=
  QuotientGroup.lift (fixedAttachment R a)
    ((MulAut.conj u).toMonoidHom.comp κ) (fixedAttachment_le_kernel R κ hκ u)

@[simp] theorem markedQuotient_projection (u : Sp F) (x : stabilizer R a) :
    markedQuotient R κ hκ u (fixedProjection R a x) = u * κ x * u⁻¹ := by
  exact QuotientGroup.lift_mk' (fixedAttachment R a) (fixedAttachment_le_kernel R κ hκ u) x

theorem markedQuotient_onto (honto : Function.Surjective κ) (u : Sp F) :
    Function.Surjective (markedQuotient R κ hκ u) :=
  QuotientGroup.lift_surjective_of_surjective _ _ ((MulAut.conj u).surjective.comp honto) _

theorem markedQuotient_kernel (u : Sp F) :
    (markedQuotient R κ hκ u).ker = layerImage R a (Q R a) := by
  have he := QuotientGroup.ker_lift (fixedAttachment R a)
    ((MulAut.conj u).toMonoidHom.comp κ) (fixedAttachment_le_kernel R κ hκ u)
  change (markedQuotient R κ hκ u).ker =
    (((MulAut.conj u).toMonoidHom.comp κ).ker).map (fixedProjection R a) at he
  rw [he]
  change (MonoidHom.ker _).map _ = ((Q R a).subgroupOf _).map _
  congr 1
  ext x
  change u * κ x * u⁻¹ = 1 ↔ x.val ∈ Q R a
  rw [show (u * κ x * u⁻¹ = 1) ↔ κ x = 1 from (MulAut.conj u).map_eq_one_iff]
  exact show x ∈ κ.ker ↔ x ∈ (Q R a).subgroupOf _ from hκ ▸ Iff.rfl

/-- The original preimage of the point radical in the retained marking. -/
@[expose] def markedPointCore (u : Sp F) : Subgroup (FreeAmalgam R) :=
  (pointRadicalAmbient.comap ((MulAut.conj u).toMonoidHom.comp κ)).map
    (stabilizer R a).subtype

/-- The point-core image is the full point-radical preimage after quotienting. -/
theorem markedPointCore_image (u : Sp F) :
    layerImage R a (markedPointCore R κ u) =
      pointRadicalAmbient.comap (markedQuotient R κ hκ u) := by
  rw [layerImage,markedPointCore,subgroupOf_map_subtype_eq]
  have he : ((MulAut.conj u).toMonoidHom.comp κ) =
      (markedQuotient R κ hκ u).comp (fixedProjection R a) := by ext x; rfl
  rw [he,←comap_comap]
  exact map_comap_eq_self_of_surjective (f := fixedProjection R a)
    (QuotientGroup.mk'_surjective _) _

/-- The source centralizer of Q-one modulo the actual critical commutator. -/
@[expose] def relativeCentralizer (z : Vertex R) (u : Sp F) :
    Subgroup (FixedQuotient R a) :=
  commutatorPreimage (layerImage R a (Z R a) ⊔ layerImage R a (Z R z))
    (layerImage R a (markedPointCore R κ u))
    (layerImage R a ⁅Z R a,Z R z⁆)

theorem layerImage_commutator (B C : Subgroup (FreeAmalgam R))
    (hB : B ≤ stabilizer R a) (hC : C ≤ stabilizer R a) :
    layerImage R a ⁅B,C⁆ = ⁅layerImage R a B,layerImage R a C⁆ := by
  rw [layerImage,SubgroupTransport.subgroupOf_commutator B C hB hC,map_commutator]
  rfl

/-- Whole-core collapse makes the full original Z image the natural kernel. -/
theorem whole_layer_eq_core {g : Geometry R}
    (hb : g.b R = 2) (ha : color R a = false)
    (hwhole : Q R a = U R a ⊔ fixedCore R a) :
    layerImage R a (Z R a) = layerImage R a (Q R a) := by
  have hZQ : Z R a ≤ Q R a :=
    (g.omega_bound a ha (by rw [g.distance_constant a ha]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _)
  have hQS : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  have hUS := ((U_le_Z a).trans hZQ).trans hQS
  have hDS := (show fixedCore R a ≤ Q R a from inf_le_left).trans hQS
  apply le_antisymm (map_mono (subgroupOf_mono _ hZQ))
  rw [hwhole,subgroupOf_sup hUS hDS,Subgroup.map_sup]
  apply sup_le
  · exact map_mono (subgroupOf_mono _ (U_le_Z a))
  · have he : layerImage R a (fixedCore R a) = ⊥ := QuotientGroup.map_mk'_self _
    exact he.le.trans bot_le

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
