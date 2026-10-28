module
public import Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions.Restriction
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.PGroupCore

/-!
# The residual quotient action of a native flag automorphism

Restriction to the plane endpoint preserves its characteristic solvable
residual. Transport through the literal subtype image and then divide by the
characteristic two-core. The representative equations retain the ambient
actor, independently of a choice of quotient coordinates.

This is the restriction step for the U₅(4) automorphism assertion in
Aschbacher–Smith F.4.29(2), printed p.289 of refs/quasithin.pdf.
It does not assert rigidity or matrix representation of the whole actor.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms
open Subgroup NativeAmalgamActions
variable {G : Type*} [Group G] (P Q : Subgroup G)

def rightEndpointAction : flagAutomorphisms P Q →* MulAut Q where
  toFun a := (a.val.subgroupMap Q).trans (MulEquiv.subgroupCongr a.property.2)
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

@[simp] theorem rightEndpointAction_val (a : flagAutomorphisms P Q) (x : Q) :
    (rightEndpointAction P Q a x).val = a.val x.val := rfl

def rightResidualAction : flagAutomorphisms P Q →* MulAut (solvableResidual Q) :=
  (MulAut.characteristic (solvableResidual Q)).comp (rightEndpointAction P Q)

abbrev rightResidualImage := (solvableResidual Q).map Q.subtype

def rightResidualImageEquiv : solvableResidual Q ≃* rightResidualImage Q :=
  (solvableResidual Q).equivMapOfInjective Q.subtype Subtype.val_injective

def rightImageAction : flagAutomorphisms P Q →* MulAut (rightResidualImage Q) :=
  (MulAut.congr (rightResidualImageEquiv Q)).toMonoidHom.comp (rightResidualAction P Q)

@[simp] theorem rightImageAction_val (a : flagAutomorphisms P Q) (x : rightResidualImage Q) :
    (rightImageAction P Q a x).val = a.val x.val := by
  obtain ⟨x,rfl⟩ := (rightResidualImageEquiv Q).surjective x
  change ((rightResidualImageEquiv Q)
    (rightResidualAction P Q a ((rightResidualImageEquiv Q).symm
      (rightResidualImageEquiv Q x)))).val = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem rightResidualImage_preserved (a : flagAutomorphisms P Q) :
    (rightResidualImage Q).map a.val.toMonoidHom = rightResidualImage Q := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact rightImageAction_val P Q a ⟨x,hx⟩ ▸ (rightImageAction P Q a ⟨x,hx⟩).property
  · intro x hx
    obtain ⟨y,hy⟩ := (rightImageAction P Q a).surjective ⟨x,hx⟩
    exact ⟨y.val,y.property,(rightImageAction_val P Q a y).symm.trans
      (congrArg Subtype.val hy)⟩

def rightQuotientAction : flagAutomorphisms P Q →*
    MulAut (rightResidualImage Q ⧸ pCore 2 (rightResidualImage Q)) :=
  (quotientAut (pCore 2 (rightResidualImage Q))).comp (rightImageAction P Q)

@[simp] theorem rightQuotientAction_mk (a : flagAutomorphisms P Q) (x : rightResidualImage Q) :
    rightQuotientAction P Q a (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (rightImageAction P Q a x) :=
  quotientAut_apply_mk _ _ _
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms
