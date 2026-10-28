module

public import Theory.GroupTheory.SmallTwoGroupCubicClassification
public import Theory.GroupTheory.SelfCentralizingFourSymmetricFour

/-!
# Recognition from a self-centralizing normal subgroup of order four

In a group of order twenty-four, a self-centralizing normal four-subgroup
is elementary abelian. An element of order three induces a nontrivial cubic
automorphism; the small two-group cubic classification excludes the cyclic
case, and the existing faithful four-group recognition gives S₄.

This supplies the good vertex in Aschbacher–Smith F.6.5(2)(iii–iv), p.305.
-/

open Subgroup

public theorem mulEquiv_perm_four_of_selfCentralizing_normal_four {G : Type*} [Group G] [Finite G] (Q : Subgroup G) [Q.Normal]
    (hQ : IsPGroup 2 Q) (hc : Nat.card Q = 4)
    (hcent : centralizer (Q : Set G) ≤ Q) (hG : Nat.card G = 24) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hG]; decide)
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  let a : MulAut Q := MulAut.conjNormal x
  have ha3 : a ^ 3 = 1 := by
    change (MulAut.conjNormal x) ^ 3 = 1
    rw [← map_pow, hx3, map_one]
  have hane : a ≠ 1 := by
    intro he
    have hxc : x ∈ centralizer (Q : Set G) := by
      rw [mem_centralizer_iff]
      intro q hq
      have hh := congrArg (fun b : MulAut Q => (b ⟨q, hq⟩ : G)) he
      change x * q * x⁻¹ = q at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    let z : Q := ⟨x, hcent hxc⟩
    have hz : orderOf z = 3 := (Subgroup.orderOf_coe z).symm.trans hx
    have hh := hQ.orderOf_coprime (by decide : Nat.Coprime 2 3) z
    rw [hz] at hh
    norm_num at hh
  rcases elementary_or_quaternion_of_small_two_group_cubic hQ (by omega) a ha3 hane with hel | hquat
  · let : IsElementaryAbelian 2 Q := hel
    exact mulEquiv_perm_four_of_selfCentralizing_four_card_twentyfour Q hc hcent hG
  · obtain ⟨e⟩ := hquat
    have hh := Nat.card_congr e.toEquiv
    rw [hc, Nat.card_eq_fintype_card, QuaternionGroup.card] at hh
    norm_num at hh
