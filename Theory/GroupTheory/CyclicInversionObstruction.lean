module

public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Opposite actions in a cyclic involution commutator

An element of order nine inverted by t belongs to [A,⟨t⟩] whenever it
belongs to A: its square is an explicit commutator, and its fifth power
recovers the element. Two such elements in a cyclic commutator generate
the same order-nine subgroup. An operator cannot fix one and invert the
other. This is the finite cyclic obstruction needed for the two marked
torus witnesses in GLS IV, Chapter 2, Proposition 16.5.
-/

namespace Subgroup
open scoped commutatorElement

private theorem order_nine_inverted_mem_commutator
    {G : Type*} [Group G] (A : Subgroup G) {t x : G}
    (hx : orderOf x = 9) (hxA : x ∈ A)
    (htx : t * x * t⁻¹ = x⁻¹) : x ∈ ⁅A, zpowers t⁆ := by
  have hinv : t * x⁻¹ * t⁻¹ = x := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv htx
  have hc : ⁅x,t⁆ = x ^ 2 := by
    rw [commutatorElement_def]
    calc
      x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
      _ = x ^ 2 := by rw [hinv, pow_two]
  have hm := (⁅A,zpowers t⁆).pow_mem
    (commutator_mem_commutator hxA (mem_zpowers t)) 5
  rw [hc, ← pow_mul, show 2 * 5 = 9 + 1 from rfl, pow_add,
    ← hx, pow_orderOf_eq_one, one_mul, pow_one] at hm
  exact hm

/-- Two order-nine witnesses with opposite operator actions cannot lie
in a torus whose commutator with their common inverter is cyclic. -/
public theorem false_of_order_nine_opposite_actions
    {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    {t x y : G} (hcyclic : IsCyclic ↥⁅A,zpowers t⁆)
    (hx : orderOf x = 9) (hy : orderOf y = 9)
    (hxA : x ∈ A) (hyA : y ∈ A)
    (htx : t*x*t⁻¹=x⁻¹) (hty : t*y*t⁻¹=y⁻¹)
    (a : G →* G) (hax : a x = x) (hay : a y = y⁻¹) : False := by
  let C := ⁅A,zpowers t⁆
  let : IsCyclic C := hcyclic
  let xC : C := ⟨x,order_nine_inverted_mem_commutator A hx hxA htx⟩
  let yC : C := ⟨y,order_nine_inverted_mem_commutator A hy hyA hty⟩
  have hyC : orderOf yC = 9 := (Subgroup.orderOf_coe yC).symm.trans hy
  have hxy : xC ∈ zpowers yC := mem_of_pow_card_eq_one_in_cyclic (zpowers yC) (by
    rw [Nat.card_zpowers,hyC]
    apply Subtype.ext
    exact hx ▸ pow_orderOf_eq_one x)
  obtain ⟨k,hk⟩ := mem_zpowers_iff.mp hxy
  have hkG : y ^ k = x := congrArg Subtype.val hk
  have hinv : a x=x⁻¹ := by
    rw [← hkG,map_zpow]
    rw [hay,inv_zpow]
  have hx2 : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two x
      _ = x * x⁻¹ := congrArg (fun z => x*z) (hax.symm.trans hinv)
      _ = 1 := mul_inv_cancel x
  have hd : 9 ∣ 2 := hx ▸ orderOf_dvd_of_pow_eq_one hx2
  norm_num at hd

end Subgroup
