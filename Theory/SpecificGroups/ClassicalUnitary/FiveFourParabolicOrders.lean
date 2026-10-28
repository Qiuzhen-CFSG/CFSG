module

public import Theory.GroupTheory.PrimeRankCubeFree
import Mathlib.Tactic.NormNum

/-!
# Order bounds for the two parabolics of PSU₅(4)

The odd parts of the projective line and plane parabolics have respective
orders `3² * 5² * 13` and `3² * 5 * 17`. Both are cube-free. Consequently
an order dividing a power of two times either of these numbers gives the
required odd-prime rank bound. The actual parabolic order calculations
are separate inputs; this module proves the arithmetic implication.

Source: the unitary parabolic orders underlying Aschbacher–Smith,
Theorem 0.1.2(1) and F.1.12(7), printed pp.4 and 263–264. The matrix field
has order sixteen, and the projective scalar quotient has order five.
-/

namespace Theory.SpecificGroups.UnitaryFive

/-- Neither odd part of the two projective parabolic orders has a prime cube divisor. -/
public theorem prime_cube_not_dvd_parabolic_oddOrder {p : ℕ} (hp : p.Prime)
    (plane : Bool) :
    ¬ p ^ 3 ∣ (if plane then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13) := by
  intro hd
  have hpd := (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  cases plane
  · change p ^ 3 ∣ 3 ^ 2 * 5 ^ 2 * 13 at hd
    change p ∣ 3 ^ 2 * 5 ^ 2 * 13 at hpd
    have hcases : p = 3 ∨ p = 5 ∨ p = 13 := by
      rcases hp.dvd_mul.mp hpd with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
            (hp.dvd_of_dvd_pow h))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
            (hp.dvd_of_dvd_pow h)))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
    rcases hcases with rfl | rfl | rfl <;> norm_num at hd
  · change p ^ 3 ∣ 3 ^ 2 * 5 * 17 at hd
    change p ∣ 3 ^ 2 * 5 * 17 at hpd
    have hcases : p = 3 ∨ p = 5 ∨ p = 17 := by
      rcases hp.dvd_mul.mp hpd with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
            (hp.dvd_of_dvd_pow h))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
    rcases hcases with rfl | rfl | rfl <;> norm_num at hd

/-- The two projective order formulas imply the odd-prime rank bound. -/
public theorem primeRank_le_two_of_parabolic_order_dvd
    {H : Type*} [Group H] [Finite H] (a : ℕ) (plane : Bool)
    (hc : Nat.card H ∣ 2 ^ a *
      (if plane then 3 ^ 2 * 5 * 17 else 3 ^ 2 * 5 ^ 2 * 13))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : primeRank p H ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_cube_not_dvd
  intro hd
  apply prime_cube_not_dvd_parabolic_oddOrder hp plane
  exact ((ho.coprime_two_right.pow 3 a).dvd_mul_left).mp (hd.trans hc)

end Theory.SpecificGroups.UnitaryFive
