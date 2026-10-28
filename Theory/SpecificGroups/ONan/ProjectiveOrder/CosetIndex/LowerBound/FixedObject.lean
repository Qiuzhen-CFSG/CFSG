module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.Setup
public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.FixedPlane
public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.LowerBound.RowSpaceAction

/-!
# The fixed row subspace in the projective O'Nan model

The two checked identities from `FixedPlane` imply that the actual local
projective words fix its row span. The projective action is the pullback
under right multiplication, constructed in `RowSpaceAction`. No order or
recognition theorem is used. The basis has independent rows by its identity
minor. See `../source/README.md` for its construction and attribution.
-/

@[expose] public section

namespace ONan.OrderCertificate

/-- The row subspaces used for the orbit certificate. -/
abbrev RowSpace := RowSpaces.Space (Fin 45) (ZMod 7)

/-- Restrict the projective action to the specified matrix-generated model. -/
instance rowSpaceModelAction : MulAction Model RowSpace :=
  MulAction.compHom RowSpace matrixSubgroup.subtype

/-- The row span of the kernel-checked invariant eight-space. -/
def fixedPlane : RowSpace := LinearMap.range fixedPlaneRows.vecMulLinear

/-- A linear lift computes the action of its projective model element. -/
theorem rowSpace_smul_of_lift (g : Model)
    (l : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7))
    (h : g.val = Matrix.ProjGenLinGroup.mk l) (S : RowSpace) : g • S = l • S := by
  change g.val • S = l • S
  rw [h]
  rfl

/-- The fixed basis has eight independent rows. -/
theorem fixedPlaneRows_injective : Function.Injective fixedPlaneRows.vecMul :=
  RowSpaces.vecMul_injective_of_pivots fixedPlaneRows
    (Fin.castLE (by decide)) fixedPlaneRows_pivots

/-- The first local projective generator fixes the row span. -/
theorem fixedPlane_localA : localA • fixedPlane = fixedPlane := by
  change (Matrix.ProjGenLinGroup.mk (linearB⁻¹ * linearA * linearB)) • fixedPlane = fixedPlane
  exact RowSpaces.fixed_of_mul fixedPlaneRows _ fixedPlaneActionA fixedPlaneRows_localA

/-- The second local projective generator fixes the row span. -/
theorem fixedPlane_localB : localB • fixedPlane = fixedPlane := by
  change (Matrix.ProjGenLinGroup.mk (((linearA * linearB ^ 2) ^ 2)⁻¹ * linearB *
    (linearA * linearB ^ 2) ^ 2)) • fixedPlane = fixedPlane
  exact RowSpaces.fixed_of_mul fixedPlaneRows _ fixedPlaneActionB fixedPlaneRows_localB

end ONan.OrderCertificate
