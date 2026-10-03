module
public import Theory.GroupTheory.PGroup.RankOneInvolution

/-!
# Placing involutions in elementary fours

Every involution of a finite two-group containing an elementary four belongs
to an elementary four. Choose a central involution. A different involution
pairs with it; for the central involution itself, choose an involution outside
its cyclic subgroup in the given elementary subgroup.

This is the central-involution argument underlying the rank-one alternative
in Huppert, III.8.2; see also `PGroup.RankOneInvolution`.
-/

namespace IsPGroup
open Subgroup

/-- Every involution of a finite two-group containing an elementary four
belongs to an elementary four. -/
public theorem exists_elementary_four_mem_of_four_le
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup P) [IsElementaryAbelian 2 A] (hA : 4 ≤ Nat.card A)
    (t : P) (ht : orderOf t = 2) :
    ∃ V : Subgroup P, IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧ t ∈ V := by
  classical
  have htne : t ≠ 1 := by intro h; simp [h] at ht
  let : Nontrivial P := ⟨⟨t, 1, htne⟩⟩
  let : Nontrivial (center P) := hP.center_nontrivial
  have hdiv : 2 ∣ Nat.card (center P) := by
    rcases (hP.to_subgroup (center P)).card_eq_or_dvd with h | h
    · exact (ne_of_gt hP.bot_lt_center (Subgroup.card_eq_one.mp h)).elim
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center P) 2 hdiv
  have hzord : orderOf (z : P) = 2 := (Subgroup.orderOf_coe z).trans hz
  have pair (x y : P) (hx : orderOf x = 2) (hy : orderOf y = 2)
      (hne : x ≠ y) (hc : Commute x y) :
      ∃ V : Subgroup P, IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧ x ∈ V := by
    let V := closure ({x, y} : Set P)
    let : IsKleinFour V := isKleinFour_closure_pair_of_orderOf x y hx hy hne hc
    have he : IsElementaryAbelian 2 V :=
      { toIsMulCommutative := IsKleinFour.isMulCommutative
        exponent_dvd_p := by simp }
    exact ⟨V, he, IsKleinFour.card_four, subset_closure (by simp)⟩
  by_cases htz : t = (z : P)
  · have hnle : ¬ A ≤ zpowers t := by
      intro h
      have hc := card_le_of_le h
      rw [Nat.card_zpowers, ht] at hc
      omega
    obtain ⟨a, ha, hat⟩ := SetLike.not_le_iff_exists.mp hnle
    have hane : a ≠ 1 := fun h => hat (h ▸ (zpowers t).one_mem)
    have haord : orderOf a = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian a ha) hane
    exact pair t a ht haord (fun h => hat (h ▸ mem_zpowers t))
      (by rw [htz]; exact (mem_center_iff.mp z.property a).symm)
  · exact pair t z ht hzord htz (mem_center_iff.mp z.property t)

end IsPGroup
