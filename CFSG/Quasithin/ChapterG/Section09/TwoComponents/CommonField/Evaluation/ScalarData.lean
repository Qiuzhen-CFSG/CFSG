module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Interfaces

/-!
# Compatible common scalars before tensor evaluation

The scalar step in G.9.3 must align the two Schur fields on the ambient
module. An abstract isomorphism of finite fields is insufficient: every
binary constituent embedding must respect the chosen scalars. This file
states that precise intermediate obligation, without asserting its existence.

The tensor step can then work over the common field, using the actual
multiplicity space of the left constituent. The two construction steps are
independent conditional theorems; their premises must both be discharged by
the final assembly in `CommonField.Evaluation`.

Source: Aschbacher--Smith, combined manuscript, G.9.3, printed p.356,
first paragraph.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Representation

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField

universe u v

variable {G : Type u} [Group G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L L₂ : Subgroup G}

/-- Compatible scalar actions for both homogeneous restrictions. In particular,
`left_maps_linear` and `right_maps_linear` concern all binary intertwining
maps, not just a selected embedding. No tensor equivalence is included. -/
structure CommonScalarData (C : ConstituentData ρ L) (D : ConstituentData ρ L₂) where
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
  left_schur : ∀ f : IntertwiningMap C.space.toRepresentation C.space.toRepresentation,
    ∃ c : F, ∀ x, f x = c • x
  right_schur : ∀ f : IntertwiningMap D.space.toRepresentation D.space.toRepresentation,
    ∃ c : F, ∀ x, f x = c • x
  left_ambient_linear : ∀ (l : L) (c : F) (x : V), ρ l (c • x) = c • ρ l x
  right_ambient_linear : ∀ (l : L₂) (c : F) (x : V), ρ l (c • x) = c • ρ l x
  left_maps_linear : ∀ f : IntertwiningMap C.space.toRepresentation (ρ.comp L.subtype),
    ∀ (c : F) x, f (c • x) = c • f x
  right_maps_linear : ∀ f : IntertwiningMap D.space.toRepresentation (ρ.comp L₂.subtype),
    ∀ (c : F) x, f (c • x) = c • f x

attribute [instance] CommonScalarData.field CommonScalarData.binaryAlgebra
  CommonScalarData.finiteField CommonScalarData.moduleI CommonScalarData.moduleJ
  CommonScalarData.towerI CommonScalarData.towerJ CommonScalarData.finiteI
  CommonScalarData.finiteJ CommonScalarData.moduleV CommonScalarData.towerV

namespace CommonScalarData

variable {C : ConstituentData ρ L} {D : ConstituentData ρ L₂} (S : CommonScalarData C D)

instance finiteV [FiniteDimensional (ZMod 2) V] : FiniteDimensional S.F V :=
  Module.Finite.of_restrictScalars_finite (ZMod 2) S.F V

/-- The original left action on the ambient space is linear over the common field. -/
def ambientLeft : Representation S.F L V where
  toFun l :=
    { toFun := ρ l
      map_add' := (ρ l).map_add
      map_smul' := S.left_ambient_linear l }
  map_one' := by ext x; exact congrArg (fun f : Module.End (ZMod 2) V => f x) ρ.map_one
  map_mul' l j := by
    ext x
    exact congrArg (fun f : Module.End (ZMod 2) V => f x) (ρ.map_mul l j)

/-- The original right action on the ambient space is linear over the common field. -/
def ambientRight : Representation S.F L₂ V where
  toFun l :=
    { toFun := ρ l
      map_add' := (ρ l).map_add
      map_smul' := S.right_ambient_linear l }
  map_one' := by ext x; exact congrArg (fun f : Module.End (ZMod 2) V => f x) ρ.map_one
  map_mul' l j := by
    ext x
    exact congrArg (fun f : Module.End (ZMod 2) V => f x) (ρ.map_mul l j)

@[simp] theorem ambientLeft_apply (l : L) (x : V) : S.ambientLeft l x = ρ l x := rfl

@[simp] theorem ambientRight_apply (l : L₂) (x : V) : S.ambientRight l x = ρ l x := rfl

/-- Commutation is inherited from the actual subgroup actions. -/
theorem ambient_commute (hc : ⁅L, L₂⁆ = ⊥) (l : L) (j : L₂) (x : V) :
    S.ambientLeft l (S.ambientRight j x) = S.ambientRight j (S.ambientLeft l x) := by
  change ρ (l : G) (ρ (j : G) x) = ρ (j : G) (ρ (l : G) x)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  exact congrArg (fun g : G => ρ g x)
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc l.property) j j.property).symm

/-- Every binary left intertwiner upgrades to a common-field intertwiner. -/
def liftLeftMap (f : IntertwiningMap C.space.toRepresentation (ρ.comp L.subtype)) :
    IntertwiningMap S.left S.ambientLeft where
  toLinearMap :=
    { toFun := f
      map_add' := map_add f
      map_smul' := S.left_maps_linear f }
  isIntertwining' l := by
    ext x
    change f (S.left l x) = ρ l (f x)
    rw [S.left_apply]
    exact congrArg (fun t : C.space.toSubmodule →ₗ[ZMod 2] V => t x) (f.isIntertwining' l)

/-- Every binary right intertwiner upgrades to a common-field intertwiner. -/
def liftRightMap (f : IntertwiningMap D.space.toRepresentation (ρ.comp L₂.subtype)) :
    IntertwiningMap S.right S.ambientRight where
  toLinearMap :=
    { toFun := f
      map_add' := map_add f
      map_smul' := S.right_maps_linear f }
  isIntertwining' l := by
    ext x
    change f (S.right l x) = ρ l (f x)
    rw [S.right_apply]
    exact congrArg (fun t : D.space.toSubmodule →ₗ[ZMod 2] V => t x) (f.isIntertwining' l)

@[simp] theorem liftLeftMap_apply
    (f : IntertwiningMap C.space.toRepresentation (ρ.comp L.subtype))
    (x : C.space.toSubmodule) : S.liftLeftMap f x = f x := rfl

@[simp] theorem liftRightMap_apply
    (f : IntertwiningMap D.space.toRepresentation (ρ.comp L₂.subtype))
    (x : D.space.toSubmodule) : S.liftRightMap f x = f x := rfl

/-- Forget the common scalars on a left intertwiner without changing its map. -/
def restrictLeftMap (f : IntertwiningMap S.left S.ambientLeft) :
    IntertwiningMap C.space.toRepresentation (ρ.comp L.subtype) where
  toLinearMap := f.toLinearMap.restrictScalars (ZMod 2)
  isIntertwining' l := by
    ext x
    change f (C.space.toRepresentation l x) = S.ambientLeft l (f x)
    rw [← S.left_apply]
    exact congrArg (fun t : C.space.toSubmodule →ₗ[S.F] V => t x) (f.isIntertwining' l)

@[simp] theorem restrictLeftMap_apply (f : IntertwiningMap S.left S.ambientLeft)
    (x : C.space.toSubmodule) : S.restrictLeftMap f x = f x := rfl

@[simp] theorem restrictLeftMap_liftLeftMap
    (f : IntertwiningMap C.space.toRepresentation (ρ.comp L.subtype)) :
    S.restrictLeftMap (S.liftLeftMap f) = f := by ext x; rfl

@[simp] theorem liftLeftMap_restrictLeftMap (f : IntertwiningMap S.left S.ambientLeft) :
    S.liftLeftMap (S.restrictLeftMap f) = f := by ext x; rfl

/-- The specified left constituent inclusion, with its actual underlying map. -/
def leftInclusion : IntertwiningMap S.left S.ambientLeft :=
  S.liftLeftMap
    { toLinearMap := C.space.toSubmodule.subtype
      isIntertwining' _ := rfl }

/-- The specified right constituent inclusion, with its actual underlying map. -/
def rightInclusion : IntertwiningMap S.right S.ambientRight :=
  S.liftRightMap
    { toLinearMap := D.space.toSubmodule.subtype
      isIntertwining' _ := rfl }

@[simp] theorem leftInclusion_apply (x : C.space.toSubmodule) : S.leftInclusion x = x := rfl

@[simp] theorem rightInclusion_apply (x : D.space.toSubmodule) : S.rightInclusion x = x := rfl

/-- The remaining geometric output over the already specified common field. -/
structure TensorEquivalence where
  tensor : V ≃ₗ[S.F] C.space.toSubmodule ⊗[S.F] D.space.toSubmodule
  left_tensor : ∀ (l : L) v,
    tensor (ρ l v) = TensorProduct.map (S.left l) 1 (tensor v)
  right_tensor : ∀ (l : L₂) v,
    tensor (ρ l v) = TensorProduct.map 1 (S.right l) (tensor v)

/-- Recover every field of the original public output from the two construction steps. -/
def toScalarTensorRealization (e : S.TensorEquivalence) : ScalarTensorRealization C D where
  F := S.F
  left := S.left
  right := S.right
  left_apply := S.left_apply
  right_apply := S.right_apply
  left_schur := S.left_schur
  right_schur := S.right_schur
  tensor := e.tensor
  left_tensor := e.left_tensor
  right_tensor := e.right_tensor

end CommonScalarData

/-- Align the two full Schur fields with their actions on the homogeneous ambient module. -/
def CommonScalarTheorem : Prop :=
  ∀ {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L L₂ : Subgroup G)
    (C : ConstituentData ρ L) (D : ConstituentData ρ L₂),
    ⁅L, L₂⁆ = ⊥ →
    Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype) →
    Nat.card C.SchurField = Nat.card D.SchurField →
    Nonempty (CommonScalarData C D)

/-- Tensor evaluation after scalar compatibility has been established. -/
def TensorEvaluationTheorem : Prop :=
  ∀ {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L L₂ : Subgroup G)
    (C : ConstituentData ρ L) (D : ConstituentData ρ L₂)
    (S : CommonScalarData C D),
    ⁅L, L₂⁆ = ⊥ →
    Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype) →
    Nonempty S.TensorEquivalence

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField
