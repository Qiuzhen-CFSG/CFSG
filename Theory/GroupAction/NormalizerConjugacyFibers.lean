module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinalities of action fibers and normalizer centralizers

A nonempty fiber of an orbit map is a translate of the stabilizer. For the
normalizer action on a subgroup, that stabilizer is the centralizer of the
element inside the normalizer. Restricting a centralizer to a smaller
subgroup preserves its intrinsic cardinality.

The proofs use translation and the natural subgroup inclusions as explicit
bijections, so no finiteness hypotheses are needed. These are the elementary
counting steps used in Glauberman, *A Characterization of the Suzuki Groups*
(1968), equations (3.2)–(3.5), pp. 83–84.
-/

open Subgroup

namespace MulAction
variable {A X : Type*} [Group A] [MulAction A X]
/-- Every nonempty orbit-map fiber has the cardinality of the stabilizer. -/
public theorem card_smul_fiber_of_witness (x y : X) (a : A) (ha : a • x = y) :
    Nat.card {g : A // g • x = y} = Nat.card (stabilizer A x) := by
  let e : {g : A // g • x = y} ≃ stabilizer A x :=
    { toFun := fun g => ⟨a⁻¹ * g, by
        change (a⁻¹ * (g : A)) • x = x
        rw [mul_smul, g.property, ← ha, inv_smul_smul]⟩
      invFun := fun g => ⟨a * g, by
        rw [mul_smul, (mem_stabilizer_iff.mp g.property), ha]⟩
      left_inv := fun g => Subtype.ext (mul_inv_cancel_left a g)
      right_inv := fun g => Subtype.ext (inv_mul_cancel_left a g) }
  exact Nat.card_congr e
end MulAction

namespace Subgroup
variable {G : Type*} [Group G]
/-- The stabilizer under normalizer conjugation is the centralizer in the normalizer. -/
public theorem stabilizer_normalizer_eq_centralizer (H : Subgroup G) (x : H) :
    MulAction.stabilizer (normalizer (H : Set G)) x =
      centralizer ({⟨x, H.le_normalizer x.property⟩} : Set (normalizer (H : Set G))) := by
  ext n
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff,
    mem_centralizer_singleton_iff, Subtype.ext_iff]
  change (n : G) * (x : G) * (n : G)⁻¹ = (x : G) ↔
    (n : G) * (x : G) = (x : G) * (n : G)
  exact mul_inv_eq_iff_eq_mul

/-- Computing a centralizer in an overgroup and then intersecting gives the same order. -/
public theorem card_inf_centralizer_subgroupOf (H K : Subgroup G) (hHK : H ≤ K) (x : H) :
    Nat.card (H.subgroupOf K ⊓
      centralizer ({⟨x, hHK x.property⟩} : Set K) : Subgroup K) =
      Nat.card (centralizer ({x} : Set H)) := by
  let e : ↥(H.subgroupOf K ⊓ centralizer ({⟨x, hHK x.property⟩} : Set K)) ≃
      centralizer ({x} : Set H) :=
    { toFun := fun c => ⟨⟨(c : K), c.property.1⟩, by
        apply mem_centralizer_singleton_iff.mpr
        apply Subtype.ext
        exact congrArg (fun z : K => (z : G)) (mem_centralizer_singleton_iff.mp c.property.2)⟩
      invFun := fun c => ⟨⟨(c : H), hHK (c : H).property⟩, ⟨(c : H).property, by
        apply mem_centralizer_singleton_iff.mpr
        apply Subtype.ext
        exact congrArg (fun z : H => (z : G)) (mem_centralizer_singleton_iff.mp c.property)⟩⟩
      left_inv := fun c => rfl
      right_inv := fun c => rfl }
  exact Nat.card_congr e
/-- A witnessed normalizer conjugacy fiber has the order of the normalizer centralizer. -/
public theorem card_normalizer_conjugacy_fiber_of_witness (H : Subgroup G) (x y : H)
    (n : normalizer (H : Set G)) (hn : H.normalizerMonoidHom n x = y) :
    Nat.card {g : normalizer (H : Set G) // H.normalizerMonoidHom g x = y} =
      Nat.card (centralizer
        ({⟨x, H.le_normalizer x.property⟩} : Set (normalizer (H : Set G)))) := by
  change Nat.card {g : normalizer (H : Set G) // g • x = y} = _
  rw [MulAction.card_smul_fiber_of_witness x y n hn, stabilizer_normalizer_eq_centralizer]

end Subgroup

