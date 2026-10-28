module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The prime factors and torus cofactors of the Ree order

For the field-size convention `q = 2^(2m+1)`, the nondefining factors of
`|²F₄(q)|` are Φ₁² Φ₂² Φ₄² Φ₆ Φ₁₂. We prove the factorization in natural
numbers, including the subtraction bounds, and exhaust the primes above
three dividing that order. At a prime dividing q-1 or q+1 the complementary
factor to the corresponding square reduces to 16 or 48, respectively.
This supplies the actual Sylow index calculation for an embedded product
torus; it does not assert the existence of any torus.

Sources: GLS3 Table 2.2 and §4.10, Eq.(4.10.1), in
`refs/KGroup/GLS3/chapter2.tex` and `chapter4.tex`. The exceptional groups
use the integer field-size convention explicitly adopted in §4.10.
-/

public section

namespace ReeF4.CentralCovers.OddPrimary

private theorem factor_four (q : ℕ) (hq : 1 ≤ q) :
    q ^ 4 - 1 = (q - 1) * (q + 1) * (q ^ 2 + 1) := by
  have hq4 : 1 ≤ q ^ 4 := one_le_pow₀ hq
  zify [hq, hq4]
  ring

private theorem factor_three (q : ℕ) :
    q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  have hq2 : q ≤ q ^ 2 := by nlinarith
  zify [hq2]
  ring

private theorem factor_six (q : ℕ) :
    q ^ 6 + 1 = (q ^ 2 + 1) * (q ^ 4 - q ^ 2 + 1) := by
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q ^ 2 - 1 : ℤ)]
  zify [hq4]
  ring

theorem prime_dvd_order_factors {m p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hd : p ∣ (2 ^ (2 * m + 1)) ^ 12 * ((2 ^ (2 * m + 1)) ^ 6 + 1) *
      ((2 ^ (2 * m + 1)) ^ 4 - 1) * ((2 ^ (2 * m + 1)) ^ 3 + 1) *
      (2 ^ (2 * m + 1) - 1)) :
    p ∣ 2 ^ (2 * m + 1) - 1 ∨ p ∣ 2 ^ (2 * m + 1) + 1 ∨
    p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 ∨
    p ∣ (2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1 ∨
    p ∣ (2 ^ (2 * m + 1)) ^ 4 - (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  let q := 2 ^ (2 * m + 1)
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (by decide)
  have hpq : ¬ p ∣ q ^ 12 := by
    intro h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h)
    have : p ≤ 2 := Nat.le_of_dvd (by decide) h2
    omega
  change p ∣ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) at hd
  rw [factor_six, factor_four q hq, factor_three] at hd
  simp only [hp.dvd_mul, hpq, false_or] at hd
  change p ∣ q - 1 ∨ p ∣ q + 1 ∨ p ∣ q ^ 2 + 1 ∨
    p ∣ q ^ 2 - q + 1 ∨ p ∣ q ^ 4 - q ^ 2 + 1
  tauto

/-- The multiplicities in the Ree order before splitting the Suzuki factors. -/
theorem order_factorization (q : ℕ) (hq : 1 ≤ q) :
    q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) =
    q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 *
      (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
  rw [factor_six, factor_four q hq, factor_three]
  ring

private theorem prime_not_dvd_sixteen {p : ℕ} (hp : p.Prime) (hlarge : 3 < p) :
    ¬ p ∣ 16 := by
  intro hd
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 from hd)
  have := Nat.le_of_dvd (by decide : 0 < 2) h2
  omega

/-- The rational product torus has prime-to-p cofactor at p dividing q-1. -/
theorem not_dvd_split_cofactor {q p : ℕ} (hq : 1 ≤ q) (hp : p.Prime)
    (hlarge : 3 < p) (hd : p ∣ q - 1) :
    ¬ p ∣ q ^ 12 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 *
      (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : q ≤ q ^ 2 := Nat.le_pow (by decide)
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q ^ 2 - 1 : ℤ)]
  have he : (q : ZMod p) = 1 := by
    have hz := (ZMod.natCast_eq_zero_iff (q - 1) p).mpr hd
    rw [Nat.cast_sub hq, Nat.cast_one] at hz
    exact sub_eq_zero.mp hz
  intro hbad
  have hz := (ZMod.natCast_eq_zero_iff _ p).mpr hbad
  push_cast [Nat.cast_sub hq2, Nat.cast_sub hq4] at hz
  rw [he] at hz
  norm_num at hz
  exact prime_not_dvd_sixteen hp hlarge
    ((ZMod.natCast_eq_zero_iff 16 p).mp hz)

/-- The norm-one product torus has prime-to-p cofactor away from three. -/
theorem not_dvd_normOne_cofactor {q p : ℕ} (hq : 1 ≤ q) (hp : p.Prime)
    (hlarge : 3 < p) (hd : p ∣ q + 1) :
    ¬ p ∣ q ^ 12 * (q - 1) ^ 2 * (q ^ 2 + 1) ^ 2 *
      (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : q ≤ q ^ 2 := Nat.le_pow (by decide)
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q ^ 2 - 1 : ℤ)]
  have he : (q : ZMod p) = -1 := by
    have hz := (ZMod.natCast_eq_zero_iff (q + 1) p).mpr hd
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz
  intro hbad
  have hz := (ZMod.natCast_eq_zero_iff _ p).mpr hbad
  push_cast [Nat.cast_sub hq, Nat.cast_sub hq2, Nat.cast_sub hq4] at hz
  rw [he] at hz
  norm_num at hz
  have h48 := (ZMod.natCast_eq_zero_iff 48 p).mp hz
  rcases hp.dvd_mul.mp (show p ∣ 16 * 3 from h48) with h16 | h3
  · exact prime_not_dvd_sixteen hp hlarge h16
  · have := Nat.le_of_dvd (by decide : 0 < 3) h3
    omega

end ReeF4.CentralCovers.OddPrimary
