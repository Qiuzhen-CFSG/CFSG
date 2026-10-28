module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.Arithmetic

/-!
# The full primary part of the third cyclotomic torus

For p > 3 dividing q²+q+1, none of the other factors in the genuine
triality order contributes a factor of p. Thus a plane of exponent
p^v_p(q²+q+1) has exactly the order of a Sylow p-subgroup. Moreover q²−1
is coprime to this exponent, as required for determinant-q² conjugation.
These are arithmetic inputs to the torus route for GLS3 §6.1; they assert
no torus existence or multiplier bound.
-/

public section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree

/-- The exponent needed for the full Sylow subgroup, including repeated primes. -/
def primaryOrder (n p : ℕ) : ℕ := p ^ (((2 ^ n) ^ 2 + 2 ^ n + 1).factorization p)

theorem primaryOrder_pos (n p : ℕ) : 0 < primaryOrder n p :=
  Nat.ordProj_pos _ _

theorem primaryOrder_dvd (n p : ℕ) : primaryOrder n p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1 :=
  Nat.ordProj_dvd _ _

private theorem other_factors {q p : ℕ} [Fact p.Prime]
    (hq : 1 ≤ q) (hp : 3 < p) (hthree : p ∣ q ^ 2 + q + 1) :
    ¬ p ∣ q ∧ ¬ p ∣ q ^ 2 - 1 ∧ ¬ p ∣ q ^ 2 - q + 1 ∧
      ¬ p ∣ q ^ 4 - q ^ 2 + 1 := by
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q * q - 1 : ℤ)]
  have h2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
  have hz : (q : ZMod p) ^ 2 + q + 1 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff _ _).mpr hthree
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have heq := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
    omega
  have hthree' : (3 : ZMod p) ≠ 0 := by
    intro h
    have heq := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp
      ((ZMod.natCast_eq_zero_iff 3 p).mp h)
    omega
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h
    simp [h] at hz
  have hquad : (q : ZMod p) ^ 2 - 1 ≠ 0 := by
    intro h
    have hminus : (q : ZMod p) - 1 ≠ 0 := by
      intro he
      apply hthree'
      linear_combination hz - ((q : ZMod p) + 2) * he
    have hplus : (q : ZMod p) + 1 ≠ 0 := by
      intro he
      have hh : (1 : ZMod p) = 0 := by
        linear_combination hz - (q : ZMod p) * he
      exact one_ne_zero hh
    apply mul_ne_zero hminus hplus
    linear_combination h
  have hsix : (q : ZMod p) ^ 2 - q + 1 ≠ 0 := by
    intro h
    apply mul_ne_zero htwo hq0
    linear_combination hz - h
  have htwelve : (q : ZMod p) ^ 4 - (q : ZMod p) ^ 2 + 1 ≠ 0 := by
    intro h
    apply mul_ne_zero htwo (pow_ne_zero 2 hq0)
    linear_combination ((q : ZMod p) ^ 2 - q + 1) * hz - h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun h => hq0 ((ZMod.natCast_eq_zero_iff _ _).mpr h)
  · intro h
    apply hquad
    simpa only [Nat.cast_sub h2, Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff _ _).mpr h
  · intro h
    apply hsix
    simpa only [Nat.cast_add, Nat.cast_sub hq2, Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff _ _).mpr h
  · intro h
    apply htwelve
    simpa only [Nat.cast_add, Nat.cast_sub hq4, Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff _ _).mpr h

/-- The conjugation determinant minus one is coprime to the full exponent. -/
theorem primaryOrder_coprime {n p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1) :
    (primaryOrder n p).Coprime ((2 ^ n) ^ 2 - 1) :=
  ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (other_factors (one_le_pow₀ (by decide)) hp hthree).2.1).pow_left _

/-- Exact primary order of the actual carrier, not just a divisibility bound. -/
theorem primaryOrder_sq (n : ℕ) (hn : 0 < n) {p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1) :
    (primaryOrder n p) ^ 2 =
      p ^ (Nat.card (Standard.BinaryCarrier n hn)).factorization p := by
  let q := 2 ^ n
  have hq : 1 < q := one_lt_pow₀ (by decide) (Nat.ne_of_gt hn)
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q * q - 1 : ℤ)]
  obtain ⟨ha, hb, hc, hd⟩ := other_factors (by omega : 1 ≤ q) hp hthree
  have hq0 : q ≠ 0 := by omega
  have hb0 : q ^ 2 - 1 ≠ 0 := by have : 1 < q ^ 2 := one_lt_pow₀ hq (by decide); omega
  have hc0 : q ^ 2 - q + 1 ≠ 0 := by omega
  have hd0 : q ^ 4 - q ^ 2 + 1 ≠ 0 := by omega
  rw [card_carrier_factorization n hn]
  change (p ^ (q ^ 2 + q + 1).factorization p) ^ 2 =
    p ^ (q ^ 12 * (q ^ 2 - 1) ^ 2 * (q ^ 2 + q + 1) ^ 2 *
      (q ^ 2 - q + 1) ^ 2 * (q ^ 4 - q ^ 2 + 1)).factorization p
  rw [Nat.factorization_mul (by positivity) hd0,
    Nat.factorization_mul (by positivity) (pow_ne_zero 2 hc0),
    Nat.factorization_mul (by positivity) (by positivity : (q ^ 2 + q + 1) ^ 2 ≠ 0),
    Nat.factorization_mul (pow_ne_zero 12 hq0) (pow_ne_zero 2 hb0)]
  simp only [Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Nat.factorization_eq_zero_of_not_dvd ha, Nat.factorization_eq_zero_of_not_dvd hb,
    Nat.factorization_eq_zero_of_not_dvd hc, Nat.factorization_eq_zero_of_not_dvd hd,
    mul_zero, zero_add, add_zero, ← pow_mul]
  rw [Nat.mul_comm 2]

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree
