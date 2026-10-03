module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.NormNum

/-!
# A C₄-square group with sign and swap actions

This is the explicit group `(C₄ × C₄) ⋊ (C₂ × C₂)` in which the two
involutions act by simultaneous inversion and by interchanging coordinates.
Its 64 elements have a unique coordinate normal form. The distinguished
index-two subgroups are the kernel of the sign coordinate (`transfer`), the
kernel of the swap coordinate (`inverterCore`), and the subgroup with even
sum of base coordinates (`extraspecialCore`).

Two explicit quaternion embeddings commute, meet in order two, and generate
`extraspecialCore`. The first quaternion subgroup together with the base
generates `transfer`. All finite calculations below are checked by Lean's
kernel. They do not invoke a small-group classification or an external
computation oracle.

This source-neutral model is intended for the order-64 local configuration
in Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`. Identifying an
actual local configuration with this model, preserving the distinguished
subgroups, is a separate theorem; no such identification is assumed here.
-/

namespace C4SquareSignSwap
public abbrev C4 := Multiplicative (ZMod 4)
public abbrev C2 := Multiplicative (ZMod 2)
public abbrev Base := C4 × C4
public abbrev Actor := C2 × C2

@[expose] public def twist (c : Actor) (x : Base) : Base :=
  let y := if c.2 = 1 then x else x.swap
  if c.1 = 1 then y else y⁻¹

private theorem twist_involutive : ∀ c : Actor, ∀ x : Base, twist c (twist c x) = x := by
  decide +kernel
private theorem twist_mul : ∀ c : Actor, ∀ x y : Base,
    twist c (x * y) = twist c x * twist c y := by
  decide +kernel

@[expose] public def action : Actor →* MulAut Base where
  toFun c :=
    { toFun := twist c
      invFun := twist c
      left_inv := by exact twist_involutive c
      right_inv := by exact twist_involutive c
      map_mul' := by exact twist_mul c }
  map_one' := by
    apply MulEquiv.ext
    exact (by decide : ∀ x : Base, twist 1 x = x)
  map_mul' := by
    intro c d
    apply MulEquiv.ext
    exact (by decide : ∀ c d : Actor, ∀ x : Base,
      twist (c * d) x = twist c (twist d x)) c d

public abbrev Model := SemidirectProduct Base Actor action
public instance : Fintype Model := Fintype.ofEquiv (Base × Actor) SemidirectProduct.equivProd.symm

@[expose] public def base : Subgroup Model where
  carrier := {g | g.right = 1}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a.right * b.right = 1; rw [ha, hb, one_mul]
  inv_mem' := by intro a ha; change a.right⁻¹ = 1; rw [ha, inv_one]

@[expose] public def transfer : Subgroup Model where
  carrier := {g | g.right.1 = 1}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a.right.1 * b.right.1 = 1; rw [ha, hb, one_mul]
  inv_mem' := by intro a ha; change a.right.1⁻¹ = 1; rw [ha, inv_one]

@[expose] public def inverterCore : Subgroup Model where
  carrier := {g | g.right.2 = 1}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a.right.2 * b.right.2 = 1; rw [ha, hb, one_mul]
  inv_mem' := by intro a ha; change a.right.2⁻¹ = 1; rw [ha, inv_one]

@[expose] public def evenSum (g : Model) : Prop :=
  (g.left.1.toAdd.val + g.left.2.toAdd.val) % 2 = 0
public instance (g : Model) : Decidable (evenSum g) := inferInstanceAs (Decidable (_ = _))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
@[expose] public def extraspecialCore : Subgroup Model where
  carrier := evenSum
  one_mem' := by change evenSum 1; decide
  mul_mem' := by change ∀ a b, evenSum a → evenSum b → evenSum (a*b); decide +kernel
  inv_mem' := by change ∀ a, evenSum a → evenSum a⁻¹; decide +kernel

public instance : DecidablePred (· ∈ base) := fun _ => inferInstanceAs (Decidable (_ = _))
public instance : DecidablePred (· ∈ transfer) := fun _ => inferInstanceAs (Decidable (_ = _))
public instance : DecidablePred (· ∈ inverterCore) := fun _ => inferInstanceAs (Decidable (_ = _))
public instance : DecidablePred (· ∈ extraspecialCore) := fun _ => inferInstanceAs (Decidable (evenSum _))

public theorem card_model : Nat.card Model = 64 := by
  rw [SemidirectProduct.card]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Base, Actor, C4, C2]
public theorem card_base : Nat.card base = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
public theorem card_transfer : Nat.card transfer = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
public theorem card_inverterCore : Nat.card inverterCore = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
public theorem card_extraspecialCore : Nat.card extraspecialCore = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] public def rotation₁ : Model := ⟨(Multiplicative.ofAdd 1, 1), 1⟩
@[expose] public def rotation₂ : Model := ⟨(1, Multiplicative.ofAdd 1), 1⟩
@[expose] public def inverter : Model := ⟨1, (Multiplicative.ofAdd 1, 1)⟩
@[expose] public def swapper : Model := ⟨1, (1, Multiplicative.ofAdd 1)⟩

set_option maxRecDepth 10000 in
public theorem normal_form : ∀ g : Model,
    g = rotation₁ ^ g.left.1.toAdd.val * rotation₂ ^ g.left.2.toAdd.val *
      inverter ^ g.right.1.toAdd.val * swapper ^ g.right.2.toAdd.val := by
  decide +kernel

public theorem rotation₁_pow_four : rotation₁ ^ 4 = 1 := by decide +kernel
public theorem rotation₂_pow_four : rotation₂ ^ 4 = 1 := by decide +kernel
public theorem inverter_pow_two : inverter ^ 2 = 1 := by decide +kernel
public theorem swapper_pow_two : swapper ^ 2 = 1 := by decide +kernel
public theorem rotations_commute : rotation₁ * rotation₂ = rotation₂ * rotation₁ := by decide +kernel
public theorem actors_commute : inverter * swapper = swapper * inverter := by decide +kernel
public theorem inverter_rotation₁ : inverter * rotation₁ * inverter⁻¹ = rotation₁⁻¹ := by decide +kernel
public theorem inverter_rotation₂ : inverter * rotation₂ * inverter⁻¹ = rotation₂⁻¹ := by decide +kernel
public theorem swapper_rotation₁ : swapper * rotation₁ * swapper⁻¹ = rotation₂ := by decide +kernel
public theorem swapper_rotation₂ : swapper * rotation₂ * swapper⁻¹ = rotation₁ := by decide +kernel

public theorem transfer_index : transfer.index = 2 := by
  have h := transfer.card_mul_index
  rw [card_transfer, card_model] at h
  omega
public theorem inverterCore_index : inverterCore.index = 2 := by
  have h := inverterCore.card_mul_index
  rw [card_inverterCore, card_model] at h
  omega
public theorem extraspecialCore_index : extraspecialCore.index = 2 := by
  have h := extraspecialCore.card_mul_index
  rw [card_extraspecialCore, card_model] at h
  omega

public instance : transfer.Normal := Subgroup.normal_of_index_eq_two transfer_index
public instance : inverterCore.Normal := Subgroup.normal_of_index_eq_two inverterCore_index
public instance : extraspecialCore.Normal := Subgroup.normal_of_index_eq_two extraspecialCore_index

@[expose] public def quaternionLeft : QuaternionGroup 2 →* Model where
  toFun q := match q with
    | .a i => (rotation₁ * rotation₂⁻¹) ^ i.val
    | .xa i => (rotation₁ * rotation₂ * swapper) * (rotation₁ * rotation₂⁻¹) ^ i.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

@[expose] public def quaternionRight : QuaternionGroup 2 →* Model where
  toFun q := match q with
    | .a i => (rotation₁ * rotation₂) ^ i.val
    | .xa i => (rotation₁ * rotation₂⁻¹ * inverter * swapper) * (rotation₁ * rotation₂) ^ i.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

public theorem quaternionLeft_injective : Function.Injective quaternionLeft := by decide +kernel
public theorem quaternionRight_injective : Function.Injective quaternionRight := by decide +kernel

public instance : DecidablePred (· ∈ quaternionLeft.range) :=
  fun g => inferInstanceAs (Decidable (∃ q, quaternionLeft q = g))
public instance : DecidablePred (· ∈ quaternionRight.range) :=
  fun g => inferInstanceAs (Decidable (∃ q, quaternionRight q = g))

set_option maxRecDepth 10000 in
public theorem quaternion_commute : ∀ a b : QuaternionGroup 2,
    quaternionLeft a * quaternionRight b = quaternionRight b * quaternionLeft a := by
  decide +kernel

public theorem quaternion_inter_card :
    Nat.card (quaternionLeft.range ⊓ quaternionRight.range : Subgroup Model) = 2 := by
  let : DecidablePred (· ∈ quaternionLeft.range ⊓ quaternionRight.range) :=
    fun g => inferInstanceAs (Decidable (g ∈ quaternionLeft.range ∧ g ∈ quaternionRight.range))
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem extraspecialCore_eq_sup :
    extraspecialCore = quaternionLeft.range ⊔ quaternionRight.range := by
  apply le_antisymm
  · have h : ∀ g : Model, g ∈ extraspecialCore → ∃ a b : QuaternionGroup 2,
        quaternionLeft a * quaternionRight b = g := by decide +kernel
    intro g hg
    obtain ⟨a, b, rfl⟩ := h g hg
    exact (quaternionLeft.range ⊔ quaternionRight.range).mul_mem
      (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right ⟨b, rfl⟩)
  · apply sup_le
    · rintro g ⟨a, rfl⟩
      exact (by decide +kernel : ∀ a : QuaternionGroup 2, quaternionLeft a ∈ extraspecialCore) a
    · rintro g ⟨a, rfl⟩
      exact (by decide +kernel : ∀ a : QuaternionGroup 2, quaternionRight a ∈ extraspecialCore) a


@[expose] public def baseEquiv : base ≃* Base where
  toFun g := g.val.left
  invFun x := ⟨⟨x, 1⟩, rfl⟩
  left_inv g := by
    apply Subtype.ext
    exact SemidirectProduct.ext rfl g.property.symm
  right_inv _ := rfl
  map_mul' g h := by
    change g.val.left * action g.val.right h.val.left = g.val.left * h.val.left
    rw [show g.val.right = 1 from g.property, map_one, MulAut.one_apply]

public instance : base.Normal := by
  change (SemidirectProduct.rightHom (φ := action)).ker.Normal
  infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
public theorem transfer_eq_sup_base_quaternionLeft : transfer = base ⊔ quaternionLeft.range := by
  apply le_antisymm
  · have h : ∀ g : Model, g ∈ transfer → ∃ a : Base, ∃ b : QuaternionGroup 2,
        SemidirectProduct.inl a * quaternionLeft b = g := by decide +kernel
    intro g hg
    obtain ⟨a, b, rfl⟩ := h g hg
    exact (base ⊔ quaternionLeft.range).mul_mem
      (Subgroup.mem_sup_left rfl) (Subgroup.mem_sup_right ⟨b, rfl⟩)
  · apply sup_le
    · exact (by decide +kernel : ∀ g : Model, g ∈ base → g ∈ transfer)
    · rintro g ⟨a, rfl⟩
      exact (by decide +kernel : ∀ a : QuaternionGroup 2, quaternionLeft a ∈ transfer) a

end C4SquareSignSwap
