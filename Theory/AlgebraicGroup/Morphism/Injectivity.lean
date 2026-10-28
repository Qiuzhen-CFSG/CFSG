module

public import Theory.AlgebraicGroup.Morphism.ClosedImage

universe u

/-! Injectivity criteria for algebraic-group morphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- If a morphism kernel lies in a closed subgroup, an isomorphism from that
subgroup onto its closed image forces the ambient morphism to be injective. -/
public theorem Morphism.injective_of_closedSubgroup_image_iso
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (B : ClosedSubgroup G)
    (hkerB : f.kernel ≤ B.toSubgroup)
    (eB : AlgebraicGroup.Iso B.carrierVariety
      (f.comp B.inclusion).imageClosedSubgroup.carrierVariety)
    (heB : ∀ x,
      (f.comp B.inclusion).imageClosedSubgroup.inclusion.onPoints
        (eB.hom.onPoints x) = f.onPoints (B.inclusion.onPoints x)) :
    Function.Injective f.onPoints := by
  intro x y hxy
  have hxyker : x * y⁻¹ ∈ f.kernel := by
    apply MonoidHom.mem_ker.mpr
    rw [f.onPoints.map_mul, f.onPoints.map_inv, hxy, mul_inv_cancel]
  have hxyB := hkerB hxyker
  let b : Variety.Point B.carrierVariety :=
    B.pointEquiv.symm ⟨x * y⁻¹, hxyB⟩
  have hbval : B.inclusion.onPoints b = x * y⁻¹ := by
    change (B.pointEquiv b).val = x * y⁻¹
    dsimp only [b]
    rw [B.pointEquiv.apply_symm_apply]
  have heBone : eB.hom.onPoints b = 1 := by
    apply (f.comp B.inclusion).imageClosedSubgroup.inclusion_injective
    rw [heB]
    change f.onPoints (B.inclusion.onPoints b) = 1
    rw [hbval]
    exact hxyker
  have hbOne : b = 1 := by
    calc
      b = eB.inv.onPoints (eB.hom.onPoints b) := (eB.hom_inv_id b).symm
      _ = eB.inv.onPoints 1 := congrArg eB.inv.onPoints heBone
      _ = 1 := eB.inv.onPoints.map_one
  have hprod : x * y⁻¹ = 1 := by
    rw [← hbval, hbOne]
    exact B.inclusion.onPoints.map_one
  exact mul_inv_eq_one.mp hprod

end Theory.AlgebraicGroup
