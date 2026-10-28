module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic

/-!
# The three-part of the Ree order

For q ≡ 2 mod 3, the Ree order factors as 3(q+1)² times a factor
prime to three. Consequently a subgroup of order 3|q+1|₃² is Sylow.
The proof uses q = 3s+2 to write (q²-q+1)/3 as 3s²+3s+1 and
does not bound the valuation of q+1. It consumes an explicit group-order
equality rather than asserting the order of the Ree model.

Source: the order convention accompanying GLS3 Example 2.6.3 and the
three-local SU₃ row of Table 4.7.3A; here q is the field size.
-/

public section
namespace ReeF4.CentralCovers.OddPrimary.Three

theorem fieldSize_mod_three (m : ℕ) : 2 ^ (2 * m + 1) % 3 = 2 := by
  rw [pow_add, pow_mul]
  simp [Nat.mul_mod, Nat.pow_mod]

/-- The Ree order after extracting the two factors q+1 and the extra three. -/
def orderCofactor (q : ℕ) : ℕ :=
  q ^ 12 * (q ^ 6 + 1) * (q - 1) ^ 2 * (q ^ 2 + 1) *
    (3 * (q / 3) ^ 2 + 3 * (q / 3) + 1)

theorem order_factorization {q : ℕ} (hq : q % 3 = 2) :
    q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) =
      (q + 1) ^ 2 * 3 * orderCofactor q := by
  have he : q = 3 * (q / 3) + 2 := by omega
  have hfour : q ^ 4 - 1 = (q - 1) * (q + 1) * (q ^ 2 + 1) := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring,
      show (q ^ 2) ^ 2 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) by
        simpa [mul_comm] using Nat.sq_sub_sq (q ^ 2) 1,
      show q ^ 2 - 1 = (q - 1) * (q + 1) by
        simpa [mul_comm] using Nat.sq_sub_sq q 1]
  have hcube : q ^ 3 + 1 = (q + 1) * (3 * (q / 3) ^ 2 + 3 * (q / 3) + 1) * 3 := by
    conv_lhs => rw [he]
    conv_rhs => arg 1; arg 1; rw [he]
    ring
  rw [hfour, hcube, orderCofactor]
  ring

theorem orderCofactor_prime_to_three {q : ℕ} (hq : q % 3 = 2) :
    ¬ 3 ∣ orderCofactor q := by
  have hqm : (q - 1) % 3 = 1 := by omega
  have he : orderCofactor q % 3 = 1 := by
    simp [orderCofactor, Nat.mul_mod, Nat.add_mod, Nat.pow_mod, hq, hqm]
  intro hd
  have := Nat.mod_eq_zero_of_dvd hd
  omega

/-- A subgroup of order three times the square of the full three-part of
q+1 has index prime to three in a group with the stated Ree order. -/
theorem index_prime_to_three_of_order {G : Type*} [Group G] [Finite G]
    {q c d : ℕ} (hq : q % 3 = 2) (hc : 0 < c)
    (hcd : c * d = q + 1) (hd : ¬ 3 ∣ d)
    (horder : Nat.card G = q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1))
    (H : Subgroup G) (hH : Nat.card H = c ^ 2 * 3) : ¬ 3 ∣ H.index := by
  have hi := H.card_mul_index
  rw [hH, horder, order_factorization hq, ← hcd, mul_pow] at hi
  have hfactor : c ^ 2 * 3 * H.index = c ^ 2 * 3 * (d ^ 2 * orderCofactor q) := by
    calc
      _ = c ^ 2 * d ^ 2 * 3 * orderCofactor q := hi
      _ = _ := by ring
  have he := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < c ^ 2 * 3) hfactor
  rw [he]
  apply Nat.Prime.not_dvd_mul (by decide : Nat.Prime 3)
  · exact fun h => hd ((by decide : Nat.Prime 3).dvd_of_dvd_pow h)
  · exact orderCofactor_prime_to_three hq

end ReeF4.CentralCovers.OddPrimary.Three
