module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.Arithmetic

/-!
# The full sixth-cyclotomic primary part of the triality order

For p > 3 dividing q² − q + 1, reduction modulo p excludes every other
factor of the proved order of the genuine binary triality carrier. Thus
its p-valuation is twice the valuation of q² − q + 1. An embedded square
of cyclic groups of precisely that primary order is consequently Sylow.
The same calculation supplies the determinant coprimality needed for a
normalizer acting by q² on one generator and fixing the other.

Source: the nondefining-characteristic calculation of GLS3 §6.1, using
the actual fixed Bruhat count of §§2.3–2.4. This module constructs no torus.
-/

public section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix

/-- The sixth cyclotomic value, with natural subtraction. -/
abbrev modulus (q : ℕ) : ℕ := q ^ 2 - q + 1

/-- All the remaining factors in the actual carrier order. -/
abbrev complement (q : ℕ) : ℕ :=
  q ^ 12 * (q ^ 2 - 1) ^ 2 * (q ^ 2 + q + 1) ^ 2 * (q ^ 4 - q ^ 2 + 1)

private theorem coprime_factors {q p : ℕ} [Fact p.Prime]
    (hq : 1 ≤ q) (hp : 3 < p) (hd : p ∣ modulus q) :
    p.Coprime q ∧ p.Coprime (q ^ 2 - 1) ∧
      p.Coprime (q ^ 2 + q + 1) ∧ p.Coprime (q ^ 4 - q ^ 2 + 1) := by
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q * q - 1 : ℤ)]
  have h2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
  have hz : (q : ZMod p) ^ 2 - q + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    simpa only [modulus, Nat.cast_add, Nat.cast_sub hq2, Nat.cast_pow,
      Nat.cast_one] using h
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff 2 p).mp h)
    omega
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 3) ((ZMod.natCast_eq_zero_iff 3 p).mp h)
    omega
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h
    simp only [h, zero_pow (by decide : 2 ≠ 0), sub_zero, zero_add, one_ne_zero] at hz
  have hquad : (q : ZMod p) ^ 2 - 1 ≠ 0 := by
    intro he
    apply hthree
    linear_combination (q + 2 : ZMod p) * hz - (q + 1 : ZMod p) * he
  have hphi3 : (q : ZMod p) ^ 2 + q + 1 ≠ 0 := by
    intro he
    apply (mul_ne_zero htwo hq0)
    linear_combination he - hz
  have hphi12 : (q : ZMod p) ^ 4 - (q : ZMod p) ^ 2 + 1 ≠ 0 := by
    intro he
    apply (mul_ne_zero htwo (pow_ne_zero 2 hq0))
    linear_combination ((q : ZMod p) ^ 2 + q + 1) * hz - he
  have prime := (Fact.out : p.Prime)
  refine ⟨prime.coprime_iff_not_dvd.mpr ?_, prime.coprime_iff_not_dvd.mpr ?_,
    prime.coprime_iff_not_dvd.mpr ?_, prime.coprime_iff_not_dvd.mpr ?_⟩
  · exact fun h => hq0 ((ZMod.natCast_eq_zero_iff _ _).mpr h)
  · intro h
    apply hquad
    simpa only [Nat.cast_sub h2, Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff _ _).mpr h
  · intro h
    apply hphi3
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff _ _).mpr h
  · intro h
    apply hphi12
    simpa only [Nat.cast_add, Nat.cast_sub hq4, Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_zero_iff _ _).mpr h

/-- No other carrier-order factor contributes to this prime. -/
theorem coprime_complement {q p : ℕ} [Fact p.Prime]
    (hq : 1 ≤ q) (hp : 3 < p) (hd : p ∣ modulus q) :
    p.Coprime (complement q) := by
  obtain ⟨h0, h2, h3, h12⟩ := coprime_factors hq hp hd
  exact (((h0.pow_right 12).mul_right (h2.pow_right 2)).mul_right
    (h3.pow_right 2)).mul_right h12

/-- The determinant q² detects the lifted alternating pairing on any p-primary part. -/
theorem primary_coprime {q p : ℕ} [Fact p.Prime]
    (hq : 1 ≤ q) (hp : 3 < p) (hd : p ∣ modulus q) (k : ℕ) :
    (p ^ k).Coprime (q ^ 2 - 1) :=
  ((coprime_factors hq hp hd).2.1).pow_left k

/-- Exact p-valuation, including arbitrary repeated prime divisors. -/
theorem factorization_card {n p : ℕ} (hn : 0 < n) [Fact p.Prime]
    (hp : 3 < p) (hd : p ∣ modulus (2 ^ n)) :
    (Nat.card (Standard.BinaryCarrier n hn)).factorization p =
      2 * (modulus (2 ^ n)).factorization p := by
  have hq : 1 ≤ 2 ^ n := one_le_pow₀ (by decide)
  have hc : Nat.card (Standard.BinaryCarrier n hn) =
      complement (2 ^ n) * modulus (2 ^ n) ^ 2 := by
    rw [card_carrier_factorization]
    dsimp only [complement, modulus]
    ring
  have hpos : complement (2 ^ n) ≠ 0 := by
    intro h
    have he := hc
    rw [h, zero_mul] at he
    exact Nat.card_pos.ne' he
  rw [hc, Nat.factorization_mul hpos (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mp (coprime_complement hq hp hd)),
    zero_add, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

/-- The actual ambient Sylow placement follows from the full primary square order. -/
@[expose] noncomputable def sylowOfCard {n p : ℕ} (hn : 0 < n) [Fact p.Prime]
    (hp : 3 < p) (hd : p ∣ modulus (2 ^ n))
    (T : Subgroup (Standard.BinaryCarrier n hn))
    (hT : Nat.card T = (p ^ (modulus (2 ^ n)).factorization p) ^ 2) :
    Sylow p (Standard.BinaryCarrier n hn) :=
  Sylow.ofCard T (by rw [factorization_card hn hp hd, mul_comm 2, pow_mul]; exact hT)

@[simp] theorem sylowOfCard_coe {n p : ℕ} (hn : 0 < n) [Fact p.Prime]
    (hp : 3 < p) (hd : p ∣ modulus (2 ^ n))
    (T : Subgroup (Standard.BinaryCarrier n hn))
    (hT : Nat.card T = (p ^ (modulus (2 ^ n)).factorization p) ^ 2) :
    (sylowOfCard hn hp hd T hT : Subgroup (Standard.BinaryCarrier n hn)) = T := rfl

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
