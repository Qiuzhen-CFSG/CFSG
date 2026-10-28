module

public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.Morphism.Isogeny
public import Theory.AlgebraicGroup.Tori.Extension
public import Theory.AlgebraicGroup.Tori.Character.Image

/-!
# The connected torus above an isogeny

The identity component of the inverse image of a target torus is a torus.
Restriction of the isogeny to this connected lift is surjective and has
finite point kernel. These statements follow from the finite-kernel torus
extension theorem and surjectivity on connected preimages. Containment of
the entire ambient kernel in this torus is a separate geometric statement.

Sources: GLS3, Sections 1.4 and 1.10, in `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
universe u

namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The connected part of the inverse image of a torus. -/
@[expose] noncomputable def isogenyTorusLift
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (T : ClosedSubgroup G) : ClosedSubgroup H :=
  (φ.closedSubgroupPreimage T).identityComponentAmbient

/-- Its map back to the chosen target torus. -/
noncomputable def isogenyTorusLiftMap
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (T : ClosedSubgroup G) :
    Morphism (isogenyTorusLift φ T).carrierVariety T.carrierVariety :=
  (φ.comp (isogenyTorusLift φ T).inclusion).codRestrictClosedSubgroup T
    (fun x => (φ.closedSubgroupPreimage T).identityComponentAmbient_le
      ((isogenyTorusLift φ T).pointEquiv x).property)

theorem isogenyTorusLiftMap_apply
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (T : ClosedSubgroup G)
    (x : Variety.Point (isogenyTorusLift φ T).carrierVariety) :
    T.inclusion.onPoints ((isogenyTorusLiftMap φ T).onPoints x) =
      φ.onPoints ((isogenyTorusLift φ T).inclusion.onPoints x) := by
  unfold isogenyTorusLiftMap
  exact Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ x

theorem isogenyTorusLift_isSubtorus
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hfinite : Finite φ.kernel)
    (T : ClosedSubgroup G) (hT : IsSubtorus T) :
    IsSubtorus (isogenyTorusLift φ T) := by
  let P := φ.closedSubgroupPreimage T
  let P0 := AlgebraicGroup.identityComponentClosedSubgroup P.carrierVariety
  let : AlgebraicGroup P0.carrierVariety := P0.carrierAlgebraicGroup
  exact morphism_image_isTorus (P.inclusion.comp P0.inclusion)
    (closedSubgroupPreimage_identityComponent_isSubtorus φ hfinite T hT)

theorem isogenyTorusLiftMap_surjective
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hsurj : Function.Surjective φ.onPoints)
    (T : ClosedSubgroup G) (hT : IsSubtorus T) :
    Function.Surjective (isogenyTorusLiftMap φ T).onPoints := by
  have hTc : _root_.IsConnected (T : Set (Variety.Point G)) := by
    let e := Variety.closedSubvarietyPointHomeomorph T.isZariskiClosed
    let : ConnectedSpace (Variety.Point T.carrierVariety) :=
      connectedSpace_iff_univ.mpr hT.isConnected
    exact isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mp inferInstance)
  have himage := φ.closedSubgroupPreimage_identityComponent_image_eq hsurj T hTc
  intro y
  have hy : T.inclusion.onPoints y ∈
      (φ.comp (isogenyTorusLift φ T).inclusion).imageClosedSubgroup := by
    rw [show (φ.comp (isogenyTorusLift φ T).inclusion).imageClosedSubgroup = T
      from himage]
    exact (T.pointEquiv y).property
  rcases hy with ⟨x, hx⟩
  refine ⟨x, T.inclusion_injective ?_⟩
  exact (isogenyTorusLiftMap_apply φ T x).trans hx

theorem isogenyTorusLiftMap_kernel_finite
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hfinite : Finite φ.kernel) (T : ClosedSubgroup G) :
    Finite (isogenyTorusLiftMap φ T).kernel := by
  let S := isogenyTorusLift φ T
  let q := isogenyTorusLiftMap φ T
  let embed : q.kernel → φ.kernel := fun x => ⟨S.inclusion.onPoints x.1, by
    have h := congrArg T.inclusion.onPoints (show q.onPoints x.1 = 1 from x.2)
    rw [isogenyTorusLiftMap_apply, map_one] at h
    exact h⟩
  let : Finite φ.kernel := hfinite
  exact Finite.of_injective embed (by
    intro x y hxy
    apply Subtype.ext
    apply S.inclusion_injective
    exact congrArg (fun z : φ.kernel => z.1) hxy)

/-- The torus restriction of an isogeny is again an isogeny. -/
theorem isogenyTorusLiftMap_isIsogeny
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hφ : IsIsogeny φ)
    (T : ClosedSubgroup G) (hT : IsSubtorus T) :
    IsIsogeny (isogenyTorusLiftMap φ T) :=
  ⟨isogenyTorusLiftMap_surjective φ hφ.1 T hT,
    isogenyTorusLiftMap_kernel_finite φ hφ.2 T⟩

end Theory.AlgebraicGroup
