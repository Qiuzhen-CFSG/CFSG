module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Constituents
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.Contracts

/-!
# Separate obligations for the common-field tensor construction

The actual constituents and their finite Schur fields are already constructed
in `Constituents`. Two independent steps remain. Quasiequivalence, including
the dual case, must compare constituent dimensions and Schur-field orders.
Commuting, jointly irreducible actions with those equal field orders must then
supply compatible scalar actions and an equivariant tensor identification.

The predicates below are theorem types, not assumed inhabitants. The final
adapter proves that these precise outputs recover every field of the existing
`TensorData`, including its faithful binary embeddings and equal factor
dimensions. This adapter alone is not the source construction theorem.

Source: Aschbacher--Smith, combined manuscript, G.9.3, printed p.356,
first paragraph.
-/

@[expose] public noncomputable section
open scoped MonoidAlgebra TensorProduct
open Representation

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField

universe u v

variable {G : Type u} [Group G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L L₂ : Subgroup G}

/-- The two numerical consequences of constituent quasiequivalence (including duality).
The rings whose cardinalities are compared are the full endomorphism rings. -/
structure ConstituentComparison (C : ConstituentData ρ L) (D : ConstituentData ρ L₂) : Prop where
  binary_dimension : Module.finrank (ZMod 2) C.space.toSubmodule =
    Module.finrank (ZMod 2) D.space.toSubmodule
  schur_card : Nat.card C.SchurField = Nat.card D.SchurField

/-- A common scalar structure and equivariant tensor realization on the two
specified constituent spaces. The original binary structures are retained.
This structure asserts no existence theorem. -/
structure ScalarTensorRealization (C : ConstituentData ρ L) (D : ConstituentData ρ L₂) where
  F : Type v
  [field : Field F]
  [binaryAlgebra : Algebra (ZMod 2) F]
  [finiteField : FiniteDimensional (ZMod 2) F]
  [moduleI : Module F C.space.toSubmodule]
  [moduleJ : Module F D.space.toSubmodule]
  [towerI : IsScalarTower (ZMod 2) F C.space.toSubmodule]
  [towerJ : IsScalarTower (ZMod 2) F D.space.toSubmodule]
  [finiteI : FiniteDimensional F C.space.toSubmodule]
  [finiteJ : FiniteDimensional F D.space.toSubmodule]
  [moduleV : Module F V]
  [towerV : IsScalarTower (ZMod 2) F V]
  left : Representation F L C.space.toSubmodule
  right : Representation F L₂ D.space.toSubmodule
  left_apply : ∀ l x, left l x = C.space.toRepresentation l x
  right_apply : ∀ l x, right l x = D.space.toRepresentation l x
  left_schur : ∀ f : Representation.IntertwiningMap C.space.toRepresentation
    C.space.toRepresentation, ∃ c : F, ∀ x, f x = c • x
  right_schur : ∀ f : Representation.IntertwiningMap D.space.toRepresentation
    D.space.toRepresentation, ∃ c : F, ∀ x, f x = c • x
  tensor : V ≃ₗ[F] C.space.toSubmodule ⊗[F] D.space.toSubmodule
  left_tensor : ∀ (l : L) v,
    tensor (ρ l v) = TensorProduct.map (left l) 1 (tensor v)
  right_tensor : ∀ (l : L₂) v,
    tensor (ρ l v) = TensorProduct.map 1 (right l) (tensor v)

attribute [instance] ScalarTensorRealization.field ScalarTensorRealization.binaryAlgebra
  ScalarTensorRealization.finiteField ScalarTensorRealization.moduleI
  ScalarTensorRealization.moduleJ ScalarTensorRealization.towerI
  ScalarTensorRealization.towerJ ScalarTensorRealization.finiteI
  ScalarTensorRealization.finiteJ ScalarTensorRealization.moduleV
  ScalarTensorRealization.towerV

/-- Independent obligation: compare actual constituents of the homogeneous
restrictions under either permitted source quasiequivalence. -/
def ConstituentComparisonTheorem : Prop :=
  ∀ {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L L₂ : Subgroup G)
    (C : ConstituentData ρ L) (D : ConstituentData ρ L₂),
    (Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype) ∨
      Quasiequivalent (ρ.comp L.subtype) (Representation.dual (ρ.comp L₂.subtype))) →
    ConstituentComparison C D

/-- Independent obligation: construct the common scalars and tensor evaluation
from commutation, joint irreducibility and equal finite Schur-field orders.
No quasiequivalence, component classification, equal factor dimensions or
tensor identification is assumed. -/
def TensorRealizationTheorem : Prop :=
  ∀ {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L L₂ : Subgroup G)
    (C : ConstituentData ρ L) (D : ConstituentData ρ L₂),
    ⁅L, L₂⁆ = ⊥ →
    Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype) →
    Nat.card C.SchurField = Nat.card D.SchurField →
    Nonempty (ScalarTensorRealization C D)

namespace ScalarTensorRealization

variable {C : ConstituentData ρ L} {D : ConstituentData ρ L₂}
  (T : ScalarTensorRealization C D)

theorem restrict_left : Representation.restrictScalars (k := ZMod 2) T.left =
    C.space.toRepresentation := by
  ext l x
  exact congrArg Subtype.val (T.left_apply l x)

theorem restrict_right : Representation.restrictScalars (k := ZMod 2) T.right =
    D.space.toRepresentation := by
  ext l x
  exact congrArg Subtype.val (T.right_apply l x)

/-- The binary dimension comparison gives equal dimensions over the actual
common field, whose binary degree is positive. -/
theorem equal_dimension (h : ConstituentComparison C D) :
    Module.finrank T.F D.space.toSubmodule = Module.finrank T.F C.space.toSubmodule := by
  have hn : 0 < Module.finrank (ZMod 2) T.F := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hn
  rw [Module.finrank_mul_finrank (ZMod 2) T.F D.space.toSubmodule,
    Module.finrank_mul_finrank (ZMod 2) T.F C.space.toSubmodule]
  exact h.binary_dimension.symm

/-- Assemble the original output, including faithful binary constituent
embeddings, once the two independent construction obligations are discharged. -/
def toTensorData (h : ConstituentComparison C D) : TensorData ρ L L₂ where
  F := T.F
  I := C.space.toSubmodule
  J := D.space.toSubmodule
  left := T.left
  right := T.right
  left_irreducible := T.restrict_left.symm ▸ C.irreducible
  right_irreducible := T.restrict_right.symm ▸ D.irreducible
  left_faithful := by
    intro a b hab
    apply C.faithful
    ext x
    rw [← T.left_apply, ← T.left_apply, hab]
  right_faithful := by
    intro a b hab
    apply D.faithful
    ext x
    rw [← T.right_apply, ← T.right_apply, hab]
  left_embedding := C.space.toSubmodule.subtype
  right_embedding := D.space.toSubmodule.subtype
  left_embedding_injective := Subtype.val_injective
  right_embedding_injective := Subtype.val_injective
  left_embedding_equivariant := by
    intro l x
    rw [T.left_apply]
    rfl
  right_embedding_equivariant := by
    intro l x
    rw [T.right_apply]
    rfl
  left_schur := by
    rw [T.restrict_left]
    exact T.left_schur
  right_schur := by
    rw [T.restrict_right]
    exact T.right_schur
  tensor := T.tensor
  equal_dimension := T.equal_dimension h
  left_tensor := T.left_tensor
  right_tensor := T.right_tensor

end ScalarTensorRealization
end CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField
