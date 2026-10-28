module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Assembly
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SecondActorDisplacement
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.RadicalAction.NativePositions
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.ConjugationCoordinates

/-!
# The literal central-quotient action in the Mathieu source branch

The source marking intertwines conjugation on U/Z(U) with the native binary
matrix action and retains the original H/O₂(H) projection. Commutator images
are transported exactly. Consequently native moved-plane orders lift through
the extraspecial central line, and native displacement containments feed the
original bound [W,Wᵍ] ≤ E from 12.8.11(1).

Source: Aschbacher--Smith, Lemma 14.4.12, printed pp.1011--1012.
-/

@[expose] public section
noncomputable section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu

variable {G Q : Type*} [Group G] [Group Q] [IsMulCommutative Q]
  [Module (ZMod 2) (Additive Q)]

/-- An actual marked conjugation quotient, with its original central kernel. -/
structure CentralAction (H U : Subgroup G)
    (e : coreQuotient H ≃* ActorCatalogue.Native.Model) where
  projection : U →* Q
  surjective : Function.Surjective projection
  kernel : projection.ker = center U
  coordinates : Additive Q ≃ₗ[ZMod 2] ActorCatalogue.Native.Space
  normalizes : H ≤ normalizer (U : Set G)
  equivariant : ∀ (h : H) (u : U),
    ActorCatalogue.Native.action (ActorCatalogue.starProjection H e h)
        (coordinates (Additive.ofMul (projection u))) =
      coordinates (Additive.ofMul (projection
        ⟨(h : G) * u * (h : G)⁻¹,
          le_normalizer_iff.mp normalizes h h.property u u.property⟩))

namespace CentralAction
variable {H U : Subgroup G} {e : coreQuotient H ≃* ActorCatalogue.Native.Model}
  (d : CentralAction (Q := Q) H U e)

def image (P : Subgroup G) : Submodule (ZMod 2) ActorCatalogue.Native.Space :=
  (quotientImage U d.projection P).map d.coordinates.toLinearMap

def actor (X : Subgroup G) (hX : X ≤ H) : X →* ActorCatalogue.Native.Model :=
  (ActorCatalogue.starProjection H e).comp (Subgroup.inclusion hX)

theorem actor_range (X : Subgroup G) (hX : X ≤ H) :
    (actor (e := e) X hX).range =
      (X.subgroupOf H).map (ActorCatalogue.starProjection H e) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y, hX y.property⟩, y.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

theorem image_commutator (P X : Subgroup G) (hPU : P ≤ U) (hXH : X ≤ H) :
    d.image ⁅P,X⁆ = subspaceCommutator ActorCatalogue.Native.action (d.image P)
      ((X.subgroupOf H).map (ActorCatalogue.starProjection H e)) := by
  have hact : ∀ (x : X) (u : U),
      ModuleGeometry.coordinateRepresentation d.coordinates (actor (e := e) X hXH x)
          (Additive.ofMul (d.projection u)) =
        Additive.ofMul (d.projection
          ⟨(x : G) * u * (x : G)⁻¹,
            le_normalizer_iff.mp (hXH.trans d.normalizes) x x.property u u.property⟩) := by
    intro x u
    rw [ModuleGeometry.coordinateRepresentation_apply]
    change d.coordinates.symm (ActorCatalogue.Native.action
      (ActorCatalogue.starProjection H e ⟨x, hXH x.property⟩)
        (d.coordinates (Additive.ofMul (d.projection u)))) = _
    rw [d.equivariant, d.coordinates.symm_apply_apply]
  rw [image, quotientImage_commutator (ModuleGeometry.coordinateRepresentation d.coordinates)
    U P X (hXH.trans d.normalizes) hPU (actor (e := e) X hXH) d.projection d.surjective hact]
  have ht : ∀ (g : ActorCatalogue.Native.Model) (w : Additive Q),
      ActorCatalogue.Native.action g (d.coordinates w) =
        d.coordinates (ModuleGeometry.coordinateRepresentation d.coordinates g w) := by
    intro g w
    rw [ModuleGeometry.coordinateRepresentation_apply, d.coordinates.apply_symm_apply]
    rfl
  have hm := subspaceCommutator_map_embedding ActorCatalogue.Native.action
    (ModuleGeometry.coordinateRepresentation d.coordinates) (MonoidHom.id ActorCatalogue.Native.Model)
    d.coordinates.toLinearMap ht (actor (e := e) X hXH).range (quotientImage U d.projection P)
  simpa only [Subgroup.map_id, actor_range, image] using hm.symm

theorem image_mono {P R : Subgroup G} (h : P ≤ R) : d.image P ≤ d.image R := by
  apply Submodule.map_mono
  rintro v ⟨u, hu, rfl⟩
  exact ⟨u, h hu, rfl⟩

theorem image_card (P : Subgroup G) :
    Nat.card ((P.subgroupOf U).map d.projection) = Nat.card (d.image P) := by
  let ec : ((P.subgroupOf U).map d.projection) ≃ quotientImage U d.projection P := {
    toFun u := ⟨Additive.ofMul u, u.property⟩
    invFun u := ⟨u.val.toMul, u.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr ec).trans
    (Nat.card_congr (Submodule.equivMapOfInjective d.coordinates.toLinearMap
      d.coordinates.injective (quotientImage U d.projection P)).toEquiv)

/-- A native moved plane lifts to the source order-eight commutator. -/
theorem movedSpace_card_eight [Finite G] [IsExtraspecial 2 U]
    (T P X : Subgroup G) (hX : X ∈ XFamily H T) (hUT : U ≤ T)
    (hPU : P ≤ U) (hZP : center U ≤ P.subgroupOf U)
    (hnative : Nat.card (subspaceCommutator ActorCatalogue.Native.action (d.image P)
      ((X.subgroupOf H).map (ActorCatalogue.starProjection H e))) = 4) :
    Nat.card (movedSpace P X) = 8 := by
  apply movedSpace_card_eight_of_extraspecial_image H T U P X hX hUT
    d.normalizes hPU hZP d.projection d.kernel
  rw [d.image_card]
  change Nat.card (d.image ⁅P,X⁆) = 4
  rw [d.image_commutator P X hPU hX.le_H]
  exact hnative

theorem le_of_image_le (P E : Subgroup G) (hPU : P ≤ U)
    (hZE : center U ≤ E.subgroupOf U) (h : d.image P ≤ d.image E) : P ≤ E := by
  have hlin : quotientImage U d.projection P ≤ quotientImage U d.projection E :=
    (Submodule.map_le_map_iff_of_injective d.coordinates.injective _ _).mp h
  have hm : (P.subgroupOf U).map d.projection ≤ (E.subgroupOf U).map d.projection := hlin
  have hc := map_le_iff_le_comap.mp hm
  rw [comap_map_eq, d.kernel, sup_eq_left.mpr hZE] at hc
  intro x hx
  exact hc (show (⟨x,hPU hx⟩ : U) ∈ P.subgroupOf U from hx)

/-- Native displacement control supplies the exact original source containment,
using only 12.8.11(1) and the actual central kernel. -/
theorem movedSpace_le_of_native_bound (P X W R E : Subgroup G)
    (hPU : P ≤ U) (hXH : X ≤ H) (hWU : W ≤ U) (hRH : R ≤ H)
    (hZE : center U ≤ E.subgroupOf U) (hWR : ⁅W,R⁆ ≤ E)
    (hnative : subspaceCommutator ActorCatalogue.Native.action (d.image P)
      ((X.subgroupOf H).map (ActorCatalogue.starProjection H e)) ≤
      subspaceCommutator ActorCatalogue.Native.action (d.image W)
        ((R.subgroupOf H).map (ActorCatalogue.starProjection H e))) :
    movedSpace P X ≤ E := by
  apply d.le_of_image_le _ E
    ((commutator_mono hPU le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hXH.trans d.normalizes))) hZE
  rw [d.image_commutator P X hPU hXH]
  exact hnative.trans ((d.image_commutator W R hWU hRH).symm ▸ d.image_mono hWR)

end CentralAction
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu
