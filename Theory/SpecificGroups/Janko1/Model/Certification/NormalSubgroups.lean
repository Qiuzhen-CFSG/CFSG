module

public import Theory.GroupTheory.NormalPrimeOrder
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.Janko1.Model.Certification.OddPrimeWitnesses

/-!+# Nontrivial normal subgroups of the explicit J₁ model have even order

Choose a prime divisor of the normal subgroup's order. The order certificate
restricts it to 2, 3, 5, 7, 11, or 19. Each odd prime occurs only once, so Sylow
conjugacy forces the chosen representative into the normal subgroup. The
matrix witnesses in `OddPrimeWitnesses` then give an involution in it.

The concrete inputs are the ATLAS matrices attributed in `Model.Basic`.
-/

namespace Janko1

/-- Every nontrivial normal subgroup of the concrete matrix model has even order. -/
public theorem even_card_normal (N : Subgroup Model) (hN : N.Normal)
    (hne : N ≠ ⊥) : 2 ∣ Nat.card N := by
  let : N.Normal := hN
  have hcard : Nat.card N ≠ 1 := fun h => hne (N.eq_bot_of_card_eq h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcard
  have hpdG : p ∣ 175560 := by
    rw [← card_model]
    exact hpd.trans N.card_subgroup_dvd_card
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
    change p ∣ 2 * 2 * 2 * 3 * 5 * 7 * 11 * 19 at hpdG
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19)] at hpdG
    omega
  let : Fact p.Prime := ⟨hp⟩
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hpd
  · obtain ⟨z, hz⟩ := OddPrimeWitnesses.involution_of_3_mem N
      (N.mem_normal_of_prime_order_of_square_not_dvd hpd b orderOf_b (by
        rw [card_model]; decide))
    exact hz ▸ orderOf_dvd_natCard z
  · obtain ⟨z, hz⟩ := OddPrimeWitnesses.involution_of_5_mem N
      (N.mem_normal_of_prime_order_of_square_not_dvd hpd _ OrderCertificate.orderOf_five (by
        rw [card_model]; decide))
    exact hz ▸ orderOf_dvd_natCard z
  · obtain ⟨z, hz⟩ := OddPrimeWitnesses.involution_of_7_mem N
      (N.mem_normal_of_prime_order_of_square_not_dvd hpd _ orderOf_ab (by
        rw [card_model]; decide))
    exact hz ▸ orderOf_dvd_natCard z
  · obtain ⟨z, hz⟩ := OddPrimeWitnesses.involution_of_11_mem N
      (N.mem_normal_of_prime_order_of_square_not_dvd hpd _ OrderCertificate.orderOf_eleven (by
        rw [card_model]; decide))
    exact hz ▸ orderOf_dvd_natCard z
  · obtain ⟨z, hz⟩ := OddPrimeWitnesses.involution_of_19_mem N
      (N.mem_normal_of_prime_order_of_square_not_dvd hpd _ orderOf_abab_sq (by
        rw [card_model]; decide))
    exact hz ▸ orderOf_dvd_natCard z

end Janko1
