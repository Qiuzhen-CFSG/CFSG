module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-!
# The central involution in a quaternion extension

For any central extension of Q₈, lifts a,b of its standard generators have
central commutator of order two. Indeed, a² and b² differ by a central element,
and [a,b] differs centrally from a². Thus [a,b] is central and has square one.
Quotienting by this commutator makes the two generators commute, so it generates
the whole derived subgroup. Every automorphism fixes it.

If the kernel has exponent two, every lift of the quaternion involution has
square one. An automorphism fixing the kernel pointwise fixes every such lift.
This supplies the literal quaternion-factor lifting used in Aschbacher–Smith,
I.2.2(5), printed p.411 / PDF p.422; no multiplier or involution table is assumed.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace QuaternionBinaryExtension
variable {G : Type*} [Group G]
variable (q : G →* QuaternionGroup 2) (hk : q.ker ≤ center G)
  (hk2 : ∀ k ∈ q.ker, k ^ 2 = 1)
  (a b : G) (ha : q a = QuaternionGroup.a 1) (hb : q b = QuaternionGroup.xa 0)

include ha hb in
private theorem generated (H : Subgroup G) (hker : q.ker ≤ H) (hA : a ∈ H) (hB : b ∈ H) :
    H = ⊤ := by
  have lift (x : G) : ∃ y ∈ H, q y = q x := by
    cases h : q x with
    | a n =>
      refine ⟨a ^ n.val, H.pow_mem hA _, ?_⟩
      rw [map_pow, ha, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    | xa n =>
      refine ⟨b * a ^ n.val, H.mul_mem hB (H.pow_mem hA _), ?_⟩
      rw [map_mul, map_pow, ha, hb, QuaternionGroup.a_one_pow,
        ZMod.natCast_zmod_val, QuaternionGroup.xa_mul_a, zero_add]
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := lift x
  have hz : x * y⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  simpa using H.mul_mem (hker hz) hy

include hk ha hb in
private theorem central_of_commute (x : G) (hxa : Commute x a) (hxb : Commute x b) :
    x ∈ center G := by
  have he : centralizer ({x} : Set G) = ⊤ :=
    generated q a b ha hb _
      (fun k hk' => mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hk hk') x).symm)
      (mem_centralizer_singleton_iff.mpr hxa.symm)
      (mem_centralizer_singleton_iff.mpr hxb.symm)
  apply mem_center_iff.mpr
  intro y
  exact mem_centralizer_singleton_iff.mp (he ▸ mem_top y)

include hk ha hb in
private theorem commutator_central : ⁅a,b⁆ ∈ center G := by
  have hs : a ^ 2 * (b ^ 2)⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, map_pow, ha, hb]
    decide +kernel
  have hab : Commute (a ^ 2) b := by
    have he : a ^ 2 = (a ^ 2 * (b ^ 2)⁻¹) * b ^ 2 := by group
    rw [he]
    exact Commute.mul_left (show Commute _ b from (mem_center_iff.mp (hk hs) b).symm)
      (Commute.refl b |>.pow_left 2)
  have hd : ⁅a,b⁆ * (a ^ 2)⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_commutatorElement, map_pow, ha, hb]
    decide +kernel
  have he : ⁅a,b⁆ = (⁅a,b⁆ * (a ^ 2)⁻¹) * a ^ 2 := by group
  apply central_of_commute q hk a b ha hb
  · rw [he]
    exact Commute.mul_left (show Commute _ a from (mem_center_iff.mp (hk hd) a).symm)
      (Commute.refl a |>.pow_left 2)
  · rw [he]
    exact Commute.mul_left (show Commute _ b from (mem_center_iff.mp (hk hd) b).symm) hab

include hk ha hb in
private theorem commutator_square : ⁅a,b⁆ ^ 2 = 1 := by
  have hs : a ^ 2 * (b ^ 2)⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, map_pow, ha, hb]
    decide +kernel
  have hab : Commute (a ^ 2) b := by
    have he : a ^ 2 = (a ^ 2 * (b ^ 2)⁻¹) * b ^ 2 := by group
    rw [he]
    exact Commute.mul_left (show Commute _ b from (mem_center_iff.mp (hk hs) b).symm)
      (Commute.refl b |>.pow_left 2)
  have he := hab.commutator_eq
  rw [pow_two, commutatorElement_mul_left_eq_conj_mul,
    mem_center_iff.mp (commutator_central q hk a b ha hb) a,
    mul_inv_cancel_right, ← pow_two] at he
  exact he

include hk hk2 ha hb in
private theorem central_lift_square (x : G) (hx : q x = QuaternionGroup.a 2) : x ^ 2 = 1 := by
  have hc : q ⁅a,b⁆ = QuaternionGroup.a 2 := by
    rw [map_commutatorElement, ha, hb]
    decide +kernel
  have hd : x * ⁅a,b⁆⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx, hc, mul_inv_cancel]
  have he : x = (x * ⁅a,b⁆⁻¹) * ⁅a,b⁆ := by group
  rw [he, (show Commute (x * ⁅a,b⁆⁻¹) ⁅a,b⁆ from (mem_center_iff.mp (hk hd) _).symm).mul_pow,
    hk2 _ hd, commutator_square q hk a b ha hb, one_mul]

include hk ha hb in
private theorem commutator_eq : _root_.commutator G = zpowers ⁅a,b⁆ := by
  let D := zpowers ⁅a,b⁆
  have hD : D ≤ center G := zpowers_le.mpr (commutator_central q hk a b ha hb)
  let : D.Normal := ⟨fun d hd g => by
    rw [mem_center_iff.mp (hD hd) g, mul_inv_cancel_right]
    exact hd⟩
  let f := QuotientGroup.mk' D
  have hab : Commute (f a) (f b) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (mem_zpowers _)
  have hfker (k : G) (hk' : k ∈ q.ker) : f k ∈ center (G ⧸ D) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D y
    simpa only [map_mul] using congrArg f (mem_center_iff.mp (hk hk') x)
  have central (x : G) (hxa : Commute (f x) (f a))
      (hxb : Commute (f x) (f b)) : f x ∈ center (G ⧸ D) := by
    have he : (centralizer ({f x} : Set (G ⧸ D))).comap f = ⊤ := by
      apply generated q a b ha hb
      · intro k hk'
        exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hfker k hk') (f x)).symm
      · exact mem_centralizer_singleton_iff.mpr hxa.symm
      · exact mem_centralizer_singleton_iff.mpr hxb.symm
    apply mem_center_iff.mpr
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective D y
    exact mem_centralizer_singleton_iff.mp (show w ∈ (centralizer ({f x} : Set _)).comap f by
      rw [he]; trivial)
  have he : (center (G ⧸ D)).comap f = ⊤ :=
    generated q a b ha hb _ hfker
      (central a (Commute.refl _) hab) (central b hab.symm (Commute.refl _))
  have habG : IsMulCommutative (G ⧸ D) := by
    apply center_eq_top_iff.mp
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D y
    exact (show x ∈ (center (G ⧸ D)).comap f by rw [he]; trivial)
  exact le_antisymm (Normal.quotient_commutative_iff_commutator_le.mp habG)
    (zpowers_le.mpr (commutator_mem_commutator (mem_top a) (mem_top b)))

include hk ha hb in
private theorem commutator_order : orderOf ⁅a,b⁆ = 2 := by
  apply orderOf_eq_prime (commutator_square q hk a b ha hb)
  intro he
  have h := congrArg q he
  rw [map_commutatorElement, ha, hb, map_one] at h
  exact (by decide +kernel : ⁅(QuaternionGroup.a 1 : QuaternionGroup 2), QuaternionGroup.xa 0⁆ ≠ 1) h

include hk ha hb in
private theorem automorphism_fixes_commutator (α : MulAut G) : α ⁅a,b⁆ = ⁅a,b⁆ := by
  let D := zpowers ⁅a,b⁆
  have hα : α ⁅a,b⁆ ∈ D := by
    change α ⁅a,b⁆ ∈ zpowers ⁅a,b⁆
    rw [← commutator_eq q hk a b ha hb, map_commutatorElement]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  have ho : orderOf ⁅a,b⁆ = 2 := commutator_order q hk a b ha hb
  have h₁ : orderOf (⟨α ⁅a,b⁆, hα⟩ : D) = 2 := by
    rw [Subgroup.orderOf_mk, α.orderOf_eq, ho]
  have h₂ : orderOf (⟨⁅a,b⁆, mem_zpowers _⟩ : D) = 2 := by
    rw [Subgroup.orderOf_mk, ho]
  have hc : Nat.card D = 2 := (Nat.card_zpowers _).trans ho
  obtain ⟨v, hv, huniq⟩ := (Nat.card_eq_two_iff' (1 : D)).mp hc
  have hne₁ : (⟨α ⁅a,b⁆, hα⟩ : D) ≠ 1 := by
    intro h; rw [h, orderOf_one] at h₁; contradiction
  have hne₂ : (⟨⁅a,b⁆, mem_zpowers _⟩ : D) ≠ 1 := by
    intro h; rw [h, orderOf_one] at h₂; contradiction
  exact congrArg Subtype.val ((huniq _ hne₁).trans (huniq _ hne₂).symm)

include hk ha hb in
private theorem automorphism_fixes_lift (α : MulAut G)
    (hα : ∀ k ∈ q.ker, α k = k) (x : G)
    (hx : q x = QuaternionGroup.a 2) : α x = x := by
  have hc : q ⁅a,b⁆ = QuaternionGroup.a 2 := by
    rw [map_commutatorElement, ha, hb]
    decide +kernel
  have hd : x * ⁅a,b⁆⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx, hc, mul_inv_cancel]
  have he : (x * ⁅a,b⁆⁻¹) * ⁅a,b⁆ = x := by group
  calc
    α x = α ((x * ⁅a,b⁆⁻¹) * ⁅a,b⁆) := congrArg α he.symm
    _ = (x * ⁅a,b⁆⁻¹) * ⁅a,b⁆ := by
      rw [map_mul, hα _ hd, automorphism_fixes_commutator q hk a b ha hb α]
    _ = x := he


end QuaternionBinaryExtension

namespace MonoidHom
/-- In a central extension of Q₈ by a kernel of exponent two, every lift of
its central involution has square one and is fixed by every automorphism
fixing the kernel pointwise. -/
theorem quaternion_lift_square_and_fixed {G : Type*} [Group G]
    (q : G →* QuaternionGroup 2) (hq : Function.Surjective q)
    (hk : q.ker ≤ Subgroup.center G) (hk2 : ∀ k ∈ q.ker, k ^ 2 = 1)
    (x : G) (hx : q x = QuaternionGroup.a 2) :
    x ^ 2 = 1 ∧ ∀ α : MulAut G, (∀ k ∈ q.ker, α k = k) → α x = x := by
  obtain ⟨a, ha⟩ := hq (QuaternionGroup.a 1)
  obtain ⟨b, hb⟩ := hq (QuaternionGroup.xa 0)
  exact ⟨QuaternionBinaryExtension.central_lift_square q hk hk2 a b ha hb x hx,
    fun α hα => QuaternionBinaryExtension.automorphism_fixes_lift q hk a b ha hb α hα x hx⟩
end MonoidHom
