module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.SourceAction

/-!
# The earlier source geometry in the Mathieu branch

The hypotheses below are the original quotient marking, the Sylow-fixed
binary point and its orthogonal hyperplane, and the earlier normality and
order of Wg*. The actual native point-core calculation identifies that image
with its two-core. The scalar moved plane therefore lies in E by the proved
native radical transvection and the original 12.8.11(1) commutator bound.
The Borel residual is excluded directly from its fixation of the same point.

Source: Aschbacher--Smith, 12.8.11--12 and 14.4.2(6),14.4.12,
printed pp.853--855,1006,1011--1012.
-/

@[expose] public section
noncomputable section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu
open ModuleGeometry.Native

variable {G Q : Type*} [Group G] [Finite G] [Group Q] [IsMulCommutative Q]
  [Module (ZMod 2) (Additive Q)]

/-- Genuine earlier geometry, before any actor/moved-space calculation. -/
structure EarlierGeometry (H U V₂ W R E : Subgroup G) (S : Sylow 2 H)
    (e : coreQuotient H ≃* ActorCatalogue.Native.Model)
    (d : CentralAction (Q := Q) H U e) (Rbar : Subgroup Group) : Prop where
  core_le_sylow : U ≤ (S : Subgroup H).map H.subtype
  point_le_core : V₂ ≤ U
  center_le_point : center U ≤ V₂.subgroupOf U
  center_le_intersection : center U ≤ E.subgroupOf U
  hyperplane_le_core : W ≤ U
  conjugate_le_local : R ≤ H
  commutator_le_intersection : ⁅W,R⁆ ≤ E
  sylow_marking : (S : Subgroup H).map (ActorCatalogue.starProjection H e) = markedSylow
  point_marking : d.image V₂ = binaryLine markedVector
  hyperplane_marking : d.image W = markedPerp
  conjugate_image : (R.subgroupOf H).map (ActorCatalogue.starProjection H e) = Rbar
  conjugate_image_le : Rbar ≤ pointCentralizer
  conjugate_image_normal : pointCentralizer ≤ normalizer
    (Rbar : Set Group)
  conjugate_image_two : IsPGroup 2 Rbar
  conjugate_image_card : Nat.card Rbar = 32

namespace EarlierGeometry
variable {H U V₂ W R E : Subgroup G} {S : Sylow 2 H}
  {e : coreQuotient H ≃* ActorCatalogue.Native.Model}
  {d : CentralAction (Q := Q) H U e} {Rbar : Subgroup Group}
  (h : EarlierGeometry H U V₂ W R E S e d Rbar)
include h

omit [Finite G] in
theorem fixed_point : ∀ s : S,
    ActorCatalogue.Native.action (ActorCatalogue.starProjection H e s.val) markedVector = markedVector := by
  intro s
  have hs : ActorCatalogue.starProjection H e s.val ∈ (markedSylow : Subgroup Group) := by
    rw [← h.sylow_marking]
    exact mem_map.mpr ⟨s.val, s.property, rfl⟩
  have hv : markedVector ∈ fixedSpace representation markedSylow := by
    rw [markedSylow_fixedSpace]
    exact Submodule.mem_span_singleton_self _
  exact hv ⟨_, hs⟩

omit [Finite G] in
/-- Earlier normality and order32 determine the literal radical image. -/
theorem radical_image : (R.subgroupOf H).map (ActorCatalogue.starProjection H e) = pointRadical := by
  have hc : Nat.card (pCore 2 pointCentralizer) = 32 := by
    rw [RadicalAction.NativePositions.pointCentralizer_eq_reference]
    apply ActorCatalogue.Native.pointCentralizer_core_card markedSylow _
      ActorCatalogue.Native.referenceVector_ne_zero
    intro s
    have hv : markedVector ∈ fixedSpace representation markedSylow := by
      rw [markedSylow_fixedSpace]
      exact Submodule.mem_span_singleton_self _
    exact hv s
  rw [h.conjugate_image]
  exact ActorCatalogue.eq_twoCore_of_normal_order32 _ _ h.conjugate_image_le
    h.conjugate_image_normal h.conjugate_image_two h.conjugate_image_card hc

omit h in
theorem first_image : ((firstActor H).subgroupOf H).map (ActorCatalogue.starProjection H e) =
    zpowers centralScalar := by
  rw [ActorCatalogue.firstActor_eq_liftedActor H e, ActorCatalogue.liftedActor_image,
    ActorCatalogue.NativeParabolics.firstActor_eq_cubic,
    ActorCatalogue.NativeParabolics.cubic_twoResidual,
    ActorCatalogue.NativeParabolics.cubic_eq_zpowers]
  rfl

/-- The first actor's source containment now has no operator-position premise. -/
theorem first_movedSpace_le (hX : firstActor H ∈ XFamily H ((S : Subgroup H).map H.subtype)) :
    movedSpace V₂ (firstActor H) ≤ E := by
  apply d.movedSpace_le_of_native_bound V₂ (firstActor H) W R E
    h.point_le_core hX.le_H h.hyperplane_le_core h.conjugate_le_local
    h.center_le_intersection h.commutator_le_intersection
  rw [h.point_marking, h.hyperplane_marking, h.radical_image, first_image]
  exact RadicalAction.scalar_moved_le_markedPerp_radical_moved

/-- The first actual commutator has order eight, including its central kernel. -/
theorem first_movedSpace_card [IsExtraspecial 2 U]
    (hX : firstActor H ∈ XFamily H ((S : Subgroup H).map H.subtype)) :
    Nat.card (movedSpace V₂ (firstActor H)) = 8 := by
  apply d.movedSpace_card_eight _ V₂ (firstActor H) hX h.core_le_sylow
    h.point_le_core h.center_le_point
  rw [h.point_marking, first_image]
  change Nat.card (subspaceCommutator representation (binaryLine markedVector)
    (zpowers centralScalar)) = 4
  rw [scalar_moved_line_eq_point, binaryPoint_card markedVector_ne_zero]

/-- The actual Borel residual fixes the original marked quotient point, so
its commutator remains in the central line and it cannot belong to Y. -/
theorem borel_not_mem_YFamily [IsExtraspecial 2 U]
    (B : Subgroup Group) (hB : B ≤ ActorCatalogue.Native.pointCentralizer markedVector) :
    borelActor (ActorCatalogue.sourceBorel H e B) ∉
      YFamily H ((S : Subgroup H).map H.subtype) V₂ E := by
  let X := borelActor (ActorCatalogue.sourceBorel H e B)
  have hXH : X ≤ H := by
    change borelActor (ActorCatalogue.sourceBorel H e B) ≤ H
    rw [ActorCatalogue.borelActor_eq_liftedActor]
    exact ActorCatalogue.liftedActor_le H e B
  have hzero : d.image (movedSpace V₂ X) = ⊥ := by
    change d.image ⁅V₂,X⁆ = ⊥
    rw [d.image_commutator V₂ X h.point_le_core hXH, h.point_marking]
    have hxim : (X.subgroupOf H).map (ActorCatalogue.starProjection H e) = twoResidual B := by
      rw [show X = ActorCatalogue.liftedActor H e B from
        ActorCatalogue.borelActor_eq_liftedActor H e B, ActorCatalogue.liftedActor_image]
    rw [hxim]
    apply (subspaceCommutator_eq_bot_iff _ _ _).mpr
    intro w hw a
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul]
    exact congrArg (fun y => c • y) (hB (map_subtype_le _ a.property))
  have himage : ((movedSpace V₂ X).subgroupOf U).map d.projection = ⊥ := by
    have hz : quotientImage U d.projection (movedSpace V₂ X) = ⊥ := by
      apply (Submodule.map_injective_of_injective d.coordinates.injective)
      rw [Submodule.map_bot]
      exact hzero
    ext x
    constructor
    · intro hx
      have hx' : Additive.ofMul x ∈ quotientImage U d.projection (movedSpace V₂ X) := hx
      rw [hz] at hx'
      exact hx'
    · intro hx
      exact hx ▸ one_mem _
  have hMU : movedSpace V₂ X ≤ U :=
    (commutator_mono h.point_le_core le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hXH.trans d.normalizes))
  have hsmall := card_le_of_le ((Subgroup.map_eq_bot_iff _).mp himage)
  have hcard : Nat.card ((movedSpace V₂ X).subgroupOf U) = Nat.card (movedSpace V₂ X) :=
    Nat.card_congr (subgroupOfEquivOfLe hMU).toEquiv
  rw [hcard, d.kernel, IsExtraspecial.center_order_p 2 U] at hsmall
  intro hy
  have he := hy.2.1
  change Nat.card (movedSpace V₂ X) = 8 at he
  omega

end EarlierGeometry
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu
