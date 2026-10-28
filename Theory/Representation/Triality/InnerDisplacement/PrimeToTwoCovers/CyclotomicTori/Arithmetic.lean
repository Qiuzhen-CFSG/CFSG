module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.SmallParameter
public import Mathlib.Tactic.LinearCombination


/-!
# Cyclotomic factors of the genuine binary triality order

The proved fixed Bruhat count factors as
q¹² (q²−1)² (q²+q+1)² (q²−q+1)² (q⁴−q²+1).
Thus primes outside 2(q²−1) lie in the three displayed cyclotomic factors.
For a prime dividing the last factor, its multiplicity in the entire
carrier order equals its multiplicity in that factor: reduction modulo
p shows it is coprime to the preceding factors. Primes occurring just once
there consequently have cyclic Sylow subgroups in the actual carrier.

These are arithmetic inputs to the nondefining-characteristic calculation
in GLS3 §6.1, Theorem 6.1.4. They use the genuine graph-field Bruhat count,
not the asserted multiplier table. Repeated factors still require actual
torus constructions.
-/

public section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori
open PerfectCentralCovering.OddSylow

private theorem order_factorization (q : ℕ) (hq : 1 ≤ q) :
    (q ^ 3 - 1) * (q - 1) * ((q ^ 3 + 1) * (q + 1) * (q ^ 8 + q ^ 4 + 1)) =
      (q ^ 2 - 1) ^ 2 * (q ^ 2 + q + 1) ^ 2 *
        (q ^ 2 - q + 1) ^ 2 * (q ^ 4 - q ^ 2 + 1) := by
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q * q - 1 : ℤ)]
  have h2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
  have h3 : 1 ≤ q ^ 3 := one_le_pow₀ hq
  zify [hq, h2, h3, hq2, hq4]
  ring

/-- Exact cyclotomic factorization, including the exponent-one parameter. -/
theorem card_carrier_factorization (n : ℕ) (hn : 0 < n) :
    Nat.card (Standard.BinaryCarrier n hn) =
      (2 ^ n) ^ 12 * ((2 ^ n) ^ 2 - 1) ^ 2 *
        ((2 ^ n) ^ 2 + 2 ^ n + 1) ^ 2 *
        ((2 ^ n) ^ 2 - 2 ^ n + 1) ^ 2 *
        ((2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1) := by
  rw [Standard.ConcreteBruhat.FixedCellCount.card_carrier n hn,
    Standard.ConcreteBruhat.FixedCellCount.card_borel]
  simp only [Standard.binaryParameters_q]
  have h := order_factorization (2 ^ n) (one_le_pow₀ (by decide))
  calc
    _ = (2 ^ n) ^ 12 * (((2 ^ n) ^ 3 - 1) * (2 ^ n - 1) *
      (((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) * ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1))) := by ring
    _ = _ := by rw [h]; ring

/-- Every prime in the requested branch divides one of these three factors. -/
theorem dvd_cyclotomic_of_dvd_card {n p : ℕ} (hn : 0 < n) [Fact p.Prime]
    (hp : 3 < p) (hquad : ¬ p ∣ (2 ^ n) ^ 2 - 1)
    (hcard : p ∣ Nat.card (Standard.BinaryCarrier n hn)) :
    p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 ∨ p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 ∨
      p ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1 := by
  have hp' := (Fact.out : p.Prime)
  have hq : ¬ p ∣ 2 ^ n := fun h => by
    have heq := (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp
      (hp'.dvd_of_dvd_pow h)
    omega
  rw [card_carrier_factorization n hn] at hcard
  rcases hp'.dvd_mul.mp hcard with hcard | h12
  · rcases hp'.dvd_mul.mp hcard with hcard | h6
    · rcases hp'.dvd_mul.mp hcard with hcard | h3
      · rcases hp'.dvd_mul.mp hcard with hq' | hquad'
        · exact (hq (hp'.dvd_of_dvd_pow hq')).elim
        · exact (hquad (hp'.dvd_of_dvd_pow hquad')).elim
      · exact Or.inl (hp'.dvd_of_dvd_pow h3)
    · exact Or.inr (Or.inl (hp'.dvd_of_dvd_pow h6))
  · exact Or.inr (Or.inr h12)

private theorem phi12_coprime_prefix {q p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hq : 1 ≤ q) (h12 : p ∣ q ^ 4 - q ^ 2 + 1) :
    p.Coprime (q ^ 12 * (q ^ 2 - 1) ^ 2 * (q ^ 2 + q + 1) ^ 2 *
      (q ^ 2 - q + 1) ^ 2) := by
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q * q - 1 : ℤ)]
  have h2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
  have hz : (q : ZMod p) ^ 4 - (q : ZMod p) ^ 2 + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ _).mpr h12
    simpa only [Nat.cast_add, Nat.cast_sub hq4, Nat.cast_pow, Nat.cast_one] using h
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h
    simp only [h, zero_pow (by decide : 4 ≠ 0), zero_pow (by decide : 2 ≠ 0),
      sub_zero, zero_add, one_ne_zero] at hz
  have ht : (2 : ZMod p) ≠ 0 := by
    intro h
    have heq := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
    exact hp heq
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hd
  have h := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_sub h2,
    Nat.cast_sub hq2, Nat.cast_one] at h
  have hquad : (q : ZMod p) ^ 2 - 1 ≠ 0 := by
    intro he
    have hh : (1 : ZMod p) = 0 := by
      linear_combination hz - ((q : ZMod p) ^ 2) * he
    exact one_ne_zero hh
  have h36 : ((q : ZMod p) ^ 2 + q + 1) * ((q : ZMod p) ^ 2 - q + 1) ≠ 0 := by
    intro he
    have hh : (2 : ZMod p) * (q : ZMod p) ^ 2 = 0 := by
      linear_combination he - hz
    exact (mul_ne_zero ht (pow_ne_zero _ hq0)) hh
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq0)
    (pow_ne_zero _ hquad)) (pow_ne_zero _ (mul_ne_zero_iff.mp h36).1))
    (pow_ne_zero _ (mul_ne_zero_iff.mp h36).2)) h

/-- The other factors contribute no multiplicity at a prime of the twelfth factor. -/
theorem square_dvd_card_iff_phi12 {n p : ℕ} (hn : 0 < n) [Fact p.Prime]
    (hp : p ≠ 2) (h12 : p ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1) :
    p ^ 2 ∣ Nat.card (Standard.BinaryCarrier n hn) ↔
      p ^ 2 ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1 := by
  rw [card_carrier_factorization n hn]
  exact ((phi12_coprime_prefix hp (one_le_pow₀ (by decide)) h12).pow_left 2).dvd_mul_left

/-- A prime occurring once in the twelfth factor is excluded by cyclic transfer. -/
theorem geometry_of_phi12_multiplicity_one {n p : ℕ} (hn : 0 < n) [Fact p.Prime]
    (hp : p ≠ 2) (h12 : p ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1)
    (hsq : ¬ p ^ 2 ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1) :
    Geometry p (Standard.BinaryCarrier n hn) :=
  geometry_of_not_square_dvd_card (hsq ∘ (square_dvd_card_iff_phi12 hn hp h12).mp)

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori
