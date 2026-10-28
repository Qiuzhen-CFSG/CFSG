module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Theory.AlgebraicGroup.Dimension.Group

universe u

/-! Dimension invariance under algebraic-group isomorphism -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct Cardinal

open LinearMap Submodule

variable {k : Type u} [Field k]

/-! Isomorphic affine algebraic groups have the same dimension. -/

public lemma algebraicGroupIso_dimension_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (e : AlgebraicGroup.Iso G H) :
    Variety.dimension G = Variety.dimension H := by
  rw [AlgebraicGroup.dimension_eq_identityComponent G,
    AlgebraicGroup.dimension_eq_identityComponent H]
  let hG₀z := AlgebraicGroup.identityComponent_isClosed G
  let hH₀z := AlgebraicGroup.identityComponent_isClosed H
  let F := e.hom.toVariety.restrictClosedSubvariety hG₀z hH₀z
    (fun x hx => e.hom.image_identityComponent_subset ⟨x, hx, rfl⟩)
  let I := e.inv.toVariety.restrictClosedSubvariety hH₀z hG₀z
    (fun y hy => e.inv.image_identityComponent_subset ⟨y, hy, rfl⟩)
  have hIF : ∀ x, I.toFun (F.toFun x) = x := by
    intro x
    apply (Variety.closedSubvarietyPointEquiv hG₀z).injective
    apply Subtype.ext
    rw [Variety.Morphism.restrictClosedSubvariety_apply,
      Variety.Morphism.restrictClosedSubvariety_apply]
    exact e.hom_inv_id _
  have hFI : ∀ y, F.toFun (I.toFun y) = y := by
    intro y
    apply (Variety.closedSubvarietyPointEquiv hH₀z).injective
    apply Subtype.ext
    rw [Variety.Morphism.restrictClosedSubvariety_apply,
      Variety.Morphism.restrictClosedSubvariety_apply]
    exact e.inv_hom_id _
  let eCoord := coordinateRingAlgEquivOfInverseMorphisms F I hIF hFI
  let : IsDomain (coordinateRing (Variety.closedSubvariety hG₀z)) := by
    simpa [hG₀z] using isDomain_coordinateRing_component
      (AlgebraicGroup.identityComponent G)
      (AlgebraicGroup.identityComponent_mem_irreducibleComponents G)
  let : IsDomain (coordinateRing (Variety.closedSubvariety hH₀z)) := by
    simpa [hH₀z] using isDomain_coordinateRing_component
      (AlgebraicGroup.identityComponent H)
      (AlgebraicGroup.identityComponent_mem_irreducibleComponents H)
  let eFrac : FractionRing (coordinateRing (Variety.closedSubvariety hH₀z)) ≃ₐ[k]
      FractionRing (coordinateRing (Variety.closedSubvariety hG₀z)) :=
    IsFractionRing.algEquivOfAlgEquiv eCoord
  change Algebra.trdeg k (FractionRing (coordinateRing
      (Variety.closedSubvariety hG₀z))) =
    Algebra.trdeg k (FractionRing (coordinateRing
      (Variety.closedSubvariety hH₀z)))
  exact eFrac.trdeg_eq.symm

end Theory.AlgebraicGroup
