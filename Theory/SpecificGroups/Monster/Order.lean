module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.NormNum

/-!
# The numerical order required of the Monster construction

Source: Conway et al., *Atlas of Finite Groups* (1985), entry `M`, order line.
The prime-power expression and its decimal expansion are checked here. These
arithmetic facts do not assert the existence of a group of this order.

Once the concrete construction is proved simple and its order is established,
`exists_noncommuting_of_card` supplies its nonabelian certificate: a simple
commutative group has prime order, whereas this number has the proper divisor 2.
-/

@[expose] public section

namespace Sporadic.Monster

/-- The order in the ATLAS entry, to be attained by the concrete construction. -/
def expectedOrder : ℕ :=
  2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 *
    17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71

theorem expectedOrder_decimal :
    expectedOrder = 808017424794512875886459904961710757005754368000000000 := by
  norm_num [expectedOrder]

theorem expectedOrder_pos : 0 < expectedOrder := by
  rw [expectedOrder_decimal]
  norm_num

theorem expectedOrder_not_prime : ¬ expectedOrder.Prime := by
  intro h
  have hd : 2 ∣ expectedOrder := by rw [expectedOrder_decimal]; norm_num
  have he := (Nat.dvd_prime h).mp hd
  rcases he with he | he <;> norm_num [expectedOrder_decimal] at he

/-- The final construction needs only simplicity and its independently proved
order to certify noncommuting elements. This is not an order recognition theorem. -/
theorem exists_noncommuting_of_card {G : Type*} [Group G] [IsSimpleGroup G]
    (hcard : Nat.card G = expectedOrder) : ∃ x y : G, x * y ≠ y * x := by
  classical
  by_contra h
  push Not at h
  let : IsMulCommutative G := IsMulCommutative.of_comm h
  have hp : (Nat.card G).Prime := Group.is_simple_iff_prime_card.mp inferInstance
  exact expectedOrder_not_prime (hcard ▸ hp)

end Sporadic.Monster
