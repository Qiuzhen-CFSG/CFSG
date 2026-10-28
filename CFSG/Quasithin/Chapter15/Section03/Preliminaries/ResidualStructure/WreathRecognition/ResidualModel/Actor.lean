module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction

/-!
# The cubic base of the natural orthogonal actor

The two-residual of SL₂(2) wreath C₂ is the subgroup with trivial shift and
independent cubic coordinates. Its order is nine. Normality and index eight
give one residual inclusion; every element of order dividing three vanishes
in every two-group quotient, giving the other. The coordinate equivalence
retains the actual matrices, for use in the compatible affine model.

Source: Aschbacher–Smith, 15.3.7–9, printed pp.1122–1123. The small matrix
certificates follow the calculations in Theory/GroupTheory/WreathTwoOddInverter.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03

namespace CFSG.Quasithin.Chapter15.Section03.WreathRecognition.ResidualModel

private theorem plane_cube_mul : ∀ a b : OrthogonalPlaneActor,
    a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1 := by
  decide +kernel

/-- The order-three subgroup in a definite plane actor. -/
def cubicPlane : Subgroup OrthogonalPlaneActor where
  carrier := {a | a ^ 3 = 1}
  one_mem' := one_pow 3
  mul_mem' := by exact plane_cube_mul _ _
  inv_mem' := by intro a ha; change a⁻¹ ^ 3 = 1; rw [inv_pow, ha, inv_one]

/-- The independent cubic actors, with trivial coordinate permutation. -/
def cubicBase : Subgroup OrthogonalActor where
  carrier := {a | a.right = 1 ∧ ∀ i, a.left i ∈ cubicPlane}
  one_mem' := ⟨rfl, fun _ => cubicPlane.one_mem⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨by simp [ha.1, hb.1], fun i => cubicPlane.mul_mem (ha.2 i) (hb.2 _)⟩
  inv_mem' := by
    intro a ha
    exact ⟨by simp [ha.1], fun i => cubicPlane.inv_mem (ha.2 _)⟩

/-- Coordinatewise conjugation preserves the cubic base. -/
instance cubicBase_normal : cubicBase.Normal where
  conj_mem a ha b := by
    refine ⟨by simp [ha.1], ?_⟩
    intro i
    change ((b * a * b⁻¹).left i) ^ 3 = 1
    have hi : (b * a * b⁻¹).left i =
        b.left i * a.left (b.right⁻¹ * i) * (b.left i)⁻¹ := by simp [ha.1]
    rw [hi, conj_pow, show (a.left (b.right⁻¹ * i)) ^ 3 = 1 from ha.2 _]
    simp

/-- Identify the cubic base with its two literal matrix coordinates. -/
def baseCoordinates : cubicBase ≃* (OrthogonalPlaneIndex → cubicPlane) where
  toFun a i := ⟨a.val.left i, a.property.2 i⟩
  invFun v := ⟨⟨fun i => v i, 1⟩, rfl, fun i => (v i).property⟩
  left_inv a := by
    apply Subtype.ext
    exact RegularWreathProduct.ext rfl a.property.1.symm
  right_inv _ := rfl
  map_mul' a b := by
    funext i
    apply Subtype.ext
    change a.val.left i * b.val.left (a.val.right⁻¹ * i) = a.val.left i * b.val.left i
    rw [a.property.1, inv_one, one_mul]

instance cubicPlane_membership_decidable : DecidablePred (· ∈ cubicPlane) := fun a =>
  inferInstanceAs (Decidable (a ^ 3 = 1))

/-- A cubic plane actor has order three. -/
theorem cubicPlane_card : Nat.card cubicPlane = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The independent cubic base has order nine. -/
theorem cubicBase_card : Nat.card cubicBase = 9 := by
  rw [Nat.card_congr baseCoordinates.toEquiv, Nat.card_fun, cubicPlane_card]
  norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card]

private theorem actor_card : Nat.card OrthogonalActor = 72 := by
  rw [RegularWreathProduct.card]
  have h : Nat.card OrthogonalPlaneActor = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [h]
  norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card]

/-- The cubic base is exactly the two-residual of the orthogonal actor. -/
theorem cubicBase_eq_residual :
    cubicBase = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor) := by
  have hindex : cubicBase.index = 8 := by
    have h := cubicBase.card_mul_index
    rw [cubicBase_card, actor_card] at h
    omega
  apply le_antisymm
  · intro a ha
    refine ⟨⟨a, mem_top a⟩, ?_, rfl⟩
    change (⟨a, mem_top a⟩ : (⊤ : Subgroup OrthogonalActor)) ∈ sInf
      {N : Subgroup (⊤ : Subgroup OrthogonalActor) | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}
    rw [mem_sInf]
    rintro N ⟨hN, n, hn⟩
    let := hN
    let x : (⊤ : Subgroup OrthogonalActor) := ⟨a, mem_top a⟩
    have hcube : x ^ 3 = 1 := by
      apply Subtype.ext
      have hc : (⟨a, ha⟩ : cubicBase) ^ 3 = 1 := by
        apply baseCoordinates.injective
        rw [map_pow, map_one]
        funext i
        apply Subtype.ext
        exact ha.2 i
      exact congrArg cubicBase.subtype hc
    have hd3 : orderOf (QuotientGroup.mk' N x) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hcube, map_one])
    have hd2 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ n := by
      rw [← hn, index_eq_card]
      exact _root_.orderOf_dvd_natCard _
    apply (QuotientGroup.eq_one_iff x).mp
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((by decide : Nat.Coprime 3 2).pow_right n) hd3 hd2)
  · have hnormal : (cubicBase.subgroupOf (⊤ : Subgroup OrthogonalActor)).Normal :=
      Subgroup.Normal.subgroupOf inferInstance _
    have hi : (cubicBase.subgroupOf (⊤ : Subgroup OrthogonalActor)).index = 2 ^ 3 := by
      rw [← relIndex, relIndex_top_right, hindex]
      decide
    have hle : Stellmacher.twoResidualSubgroup (⊤ : Subgroup OrthogonalActor) ≤
        cubicBase.subgroupOf (⊤ : Subgroup OrthogonalActor) := sInf_le ⟨hnormal, 3, hi⟩
    rintro a ⟨x, hx, rfl⟩
    exact hle hx

end CFSG.Quasithin.Chapter15.Section03.WreathRecognition.ResidualModel

end
