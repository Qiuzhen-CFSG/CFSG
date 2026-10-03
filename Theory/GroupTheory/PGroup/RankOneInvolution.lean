module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Mathlib.GroupTheory.PGroup

/-!
# The involution of a rank-one two-group

A nontrivial finite two-group with no elementary four has a unique involution
and hence a unique subgroup of order two. Choose an involution in the center.
Any different involution would commute with it and generate an elementary four.

This is the elementary input to the cyclic/generalized-quaternion alternative
in Huppert III.8.2, and to the rank-one centralizer reduction following
GLS, Number 2, Proposition 22.4.
-/

namespace IsPGroup
open Subgroup

/-- A finite nontrivial two-group without elementary fours has a unique
nonidentity involution, which is central. -/
public theorem exists_central_involution_of_no_elementary_four
    {R : Type*} [Group R] [Finite R] [Nontrivial R] (hR : IsPGroup 2 R)
    (hfour : ∀ V : Subgroup R, IsElementaryAbelian 2 V → Nat.card V ≠ 4) :
    ∃ z : R, orderOf z = 2 ∧ z ∈ center R ∧
      ∀ x : R, x ^ 2 = 1 → x = 1 ∨ x = z := by
  let : Nontrivial (center R) := hR.center_nontrivial
  have hdiv : 2 ∣ Nat.card (center R) := by
    rcases (hR.to_subgroup (center R)).card_eq_or_dvd with h | h
    · exact (ne_of_gt hR.bot_lt_center (Subgroup.card_eq_one.mp h)).elim
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center R) 2 hdiv
  have hzord : orderOf (z : R) = 2 := (Subgroup.orderOf_coe z).trans hz
  refine ⟨z, hzord, z.property, ?_⟩
  intro x hx
  by_cases hxone : x = 1
  · exact Or.inl hxone
  right
  by_contra hxz
  have hxord : orderOf x = 2 := orderOf_eq_prime hx hxone
  let V := closure ({x, (z : R)} : Set R)
  let : IsKleinFour V := isKleinFour_closure_pair_of_orderOf x z hxord hzord hxz
    (mem_center_iff.mp z.property x)
  have hVe : IsElementaryAbelian 2 V :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by simp }
  exact hfour V hVe IsKleinFour.card_four

/-- The no-elementary-four hypothesis supplies the unique-order-two-subgroup
hypothesis of the cyclic/generalized-quaternion theorem. -/
public theorem exists_unique_order_two_subgroup_of_no_elementary_four
    {R : Type*} [Group R] [Finite R] [Nontrivial R] (hR : IsPGroup 2 R)
    (hfour : ∀ V : Subgroup R, IsElementaryAbelian 2 V → Nat.card V ≠ 4) :
    ∃ U : Subgroup R, Nat.card U = 2 ∧
      ∀ V : Subgroup R, Nat.card V = 2 → V = U := by
  obtain ⟨z, hz, _, huniq⟩ := hR.exists_central_involution_of_no_elementary_four hfour
  refine ⟨zpowers z, by rw [Nat.card_zpowers, hz], ?_⟩
  intro V hV
  apply eq_of_le_of_card_ge
  · intro x hx
    have hpow : (⟨x, hx⟩ : V) ^ 2 = 1 := by
      rw [← hV]
      exact pow_card_eq_one'
    have hx2 : x ^ 2 = 1 := congrArg Subtype.val hpow
    rcases huniq x hx2 with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  · rw [Nat.card_zpowers, hz, hV]

end IsPGroup
