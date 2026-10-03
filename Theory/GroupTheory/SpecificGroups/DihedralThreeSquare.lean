module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic

/-!
# The element census of S₃ × S₃

The product of two dihedral groups of order six has order 36, with fifteen
involutions, eight elements of order three and twelve elements of order six.
The census is computed through powers in the concrete finite model and
transported along group equivalences. These are the counts used for Wong's
subgroup `M` in Appendix (b), p.110 of his 1964 paper.
-/

namespace DihedralGroup

private abbrev D := DihedralGroup 3 × DihedralGroup 3

private theorem sixth_power (x : D) : x ^ 6 = 1 := by
  apply Prod.ext
  · exact orderOf_dvd_iff_pow_eq_one.mp (by
      simpa only [DihedralGroup.exponent, show lcm 3 2 = 6 from rfl]
        using Monoid.order_dvd_exponent x.1)
  · exact orderOf_dvd_iff_pow_eq_one.mp (by
      simpa only [DihedralGroup.exponent, show lcm 3 2 = 6 from rfl]
        using Monoid.order_dvd_exponent x.2)

private theorem order_six_iff (x : D) :
    orderOf x = 6 ↔ x ^ 2 ≠ 1 ∧ x ^ 3 ≠ 1 := by
  have hd : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one (sixth_power x)
  have hl : orderOf x ≤ 6 := Nat.le_of_dvd (by decide) hd
  have h2 : (x ^ 2 ≠ 1) ↔ ¬ orderOf x ∣ 2 :=
    not_congr orderOf_dvd_iff_pow_eq_one.symm
  have h3 : (x ^ 3 ≠ 1) ↔ ¬ orderOf x ∣ 3 :=
    not_congr orderOf_dvd_iff_pow_eq_one.symm
  rw [h2, h3]
  interval_cases h : orderOf x <;> norm_num at *

private theorem square_census :
    Nat.card {x : D // orderOf x = 2} = 15 ∧
    Nat.card {x : D // orderOf x = 3} = 8 ∧
    Nat.card {x : D // orderOf x = 6} = 12 := by
  have h2 : (Finset.univ.filter (fun x : D => x ^ 2 = 1 ∧ x ≠ 1)).card = 15 := by
    decide +kernel
  have h3 : (Finset.univ.filter (fun x : D => x ^ 3 = 1 ∧ x ≠ 1)).card = 8 := by
    decide +kernel
  have h6 : (Finset.univ.filter (fun x : D => x ^ 2 ≠ 1 ∧ x ^ 3 ≠ 1)).card = 12 := by
    decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x : D =>
      show orderOf x = 2 ↔ x ^ 2 = 1 ∧ x ≠ 1 from orderOf_eq_prime_iff)),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h2
  · rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x : D =>
      show orderOf x = 3 ↔ x ^ 3 = 1 ∧ x ≠ 1 from orderOf_eq_prime_iff)),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h3
  · rw [Nat.card_congr (Equiv.subtypeEquivRight order_six_iff),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h6

/-- The full nonidentity element census of any actual S₃ × S₃ model. -/
public theorem square_three_census {H : Type*} [Group H]
    (e : H ≃* (DihedralGroup 3 × DihedralGroup 3)) :
    Nat.card H = 36 ∧
    Nat.card {x : H // orderOf x = 2} = 15 ∧
    Nat.card {x : H // orderOf x = 3} = 8 ∧
    Nat.card {x : H // orderOf x = 6} = 12 := by
  have ht (n : ℕ) : Nat.card {x : H // orderOf x = n} =
      Nat.card {x : DihedralGroup 3 × DihedralGroup 3 // orderOf x = n} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun x => by
      change orderOf x = n ↔ orderOf (e x) = n
      rw [e.orderOf_eq]))
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
  · simpa only [ht] using square_census

end DihedralGroup
