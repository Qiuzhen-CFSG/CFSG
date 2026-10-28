module

public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.Morphism.Isogeny
public import Theory.AlgebraicGroup.Tori.Extension

/-!
# Maximal tori above an isogeny

The ambient identity component of the inverse image of a maximal torus is
itself a maximal torus. The finite-kernel extension theorem makes it a torus,
and connected-preimage surjectivity identifies its image with the target
torus. Any larger source torus has that same image by target maximality,
and hence lies in the same connected component of the inverse image.

This is the maximality step in the incoming-isogeny argument for GLS3,
Theorem 1.12.5(b), using Sections 1.4 and 1.10
(`refs/KGroup/GLS3/Chapter1.tex`). It does not assert that the whole inverse
image is connected or that the ambient kernel lies in this component.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem subtorus_isConnected_ambient
    {G : Variety k} [AlgebraicGroup G]
    (T : ClosedSubgroup G) (hT : IsSubtorus T) :
    _root_.IsConnected (T : Set (Variety.Point G)) := by
  let : ConnectedSpace (Variety.Point T.carrierVariety) :=
    connectedSpace_iff_univ.mpr hT.isConnected
  change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
  rw [← T.range_inclusion]
  exact isConnected_range T.inclusion.toVariety.continuous

/-- The connected inverse image of a maximal torus under an isogeny is
a maximal torus of the source. The source need not itself be connected. -/
public theorem Morphism.closedSubgroupPreimage_identityComponent_isMaximalTorus
    {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (hφ : IsIsogeny φ)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T) :
    IsMaximalTorus (φ.closedSubgroupPreimage T).identityComponentAmbient := by
  let P := φ.closedSubgroupPreimage T
  let S := P.identityComponentAmbient
  have hS : IsSubtorus S := by
    let P0 := identityComponentClosedSubgroup P.carrierVariety
    let : AlgebraicGroup P0.carrierVariety := P0.carrierAlgebraicGroup
    exact morphism_image_isTorus (P.inclusion.comp P0.inclusion)
      (closedSubgroupPreimage_identityComponent_isSubtorus φ hφ.2 T hT.1)
  have hST : (φ.comp S.inclusion).imageClosedSubgroup = T :=
    φ.closedSubgroupPreimage_identityComponent_image_eq hφ.1 T
      (subtorus_isConnected_ambient T hT.1)
  refine ⟨hS, ?_⟩
  intro U hU hSU
  let q := φ.comp U.inclusion
  have hTU : T ≤ q.imageClosedSubgroup := by
    rw [← hST]
    intro y hy
    obtain ⟨s, rfl⟩ := hy
    let u : Variety.Point U.carrierVariety :=
      U.pointEquiv.symm ⟨S.inclusion.onPoints s, hSU (S.pointEquiv s).property⟩
    refine ⟨u, ?_⟩
    change φ.onPoints (U.inclusion.onPoints u) = φ.onPoints (S.inclusion.onPoints s)
    apply congrArg φ.onPoints
    exact congrArg Subtype.val (U.pointEquiv.apply_symm_apply _)
  have himage : q.imageClosedSubgroup = T :=
    hT.2 _ (morphism_image_isTorus q hU) hTU
  have hUP : U ≤ P := by
    intro x hx
    change φ.onPoints x ∈ T.toSubgroup
    rw [← himage]
    let u : Variety.Point U.carrierVariety := U.pointEquiv.symm ⟨x, hx⟩
    refine ⟨u, ?_⟩
    change φ.onPoints (U.inclusion.onPoints u) = φ.onPoints x
    apply congrArg φ.onPoints
    exact congrArg Subtype.val (U.pointEquiv.apply_symm_apply _)
  apply SetLike.coe_injective
  exact Set.Subset.antisymm
    (connected_closedSubgroup_le_identityComponentAmbient U P
      (subtorus_isConnected_ambient U hU) hUP) hSU

end Theory.AlgebraicGroup
