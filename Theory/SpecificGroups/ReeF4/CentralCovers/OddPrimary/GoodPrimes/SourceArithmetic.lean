module
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Arithmetic
public import Mathlib.Tactic
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.Coordinates

/-!
# Prime-to-p cofactors for the nonsplit Ree tori

Away from two and three, the factors Φ₁, Φ₂, Φ₄, Φ₆ and Φ₁₂ of the Ree
order have disjoint prime support. Explicit polynomial identities in ZMod p
prove the required separations. The signed Suzuki and twelfth-cyclotomic
factors are likewise disjoint, by their difference and the defining field
size. These facts give the exact cofactor bounds for the actual torus maps.

Source: GLS3 Table 2.2 and §4.10; Aschbacher–Smith I.1.1–4, pp.407–408.
-/

public section

namespace ReeF4.CentralCovers.OddPrimary.GoodPrimeArithmetic
variable {p : ℕ}

private theorem small_ne_zero (hlarge : 3 < p) {n : ℕ} (hn : 0 < n) (hn3 : n ≤ 3) :
    (n : ZMod p) ≠ 0 := by
  intro h
  have := Nat.le_of_dvd hn ((ZMod.natCast_eq_zero_iff n p).mp h)
  omega

private theorem phi4_nonzeros (hlarge : 3 < p) (x : ZMod p) (hx : x ^ 2 + 1 = 0) :
    x ≠ 0 ∧ x - 1 ≠ 0 ∧ x + 1 ≠ 0 ∧
      x ^ 2 - x + 1 ≠ 0 ∧ x ^ 4 - x ^ 2 + 1 ≠ 0 := by
  have h1 := small_ne_zero (p := p) hlarge (n := 1) (by decide) (by decide)
  have h2 := small_ne_zero (p := p) hlarge (n := 2) (by decide) (by decide)
  have h3 := small_ne_zero (p := p) hlarge (n := 3) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply h1; linear_combination hx - x * h
  · intro h; apply h2; linear_combination hx - (x + 1) * h
  · intro h; apply h2; linear_combination hx + (1 - x) * h
  · intro h; apply h1; linear_combination (1 - x) * hx + x * h
  · intro h; apply h3; linear_combination (2 - x ^ 2) * hx + h

private theorem phi6_nonzeros (hlarge : 3 < p) (x : ZMod p) (hx : x ^ 2 - x + 1 = 0) :
    x ≠ 0 ∧ x - 1 ≠ 0 ∧ x + 1 ≠ 0 ∧
      x ^ 2 + 1 ≠ 0 ∧ x ^ 4 - x ^ 2 + 1 ≠ 0 := by
  have h1 := small_ne_zero (p := p) hlarge (n := 1) (by decide) (by decide)
  have h2 := small_ne_zero (p := p) hlarge (n := 2) (by decide) (by decide)
  have h3 := small_ne_zero (p := p) hlarge (n := 3) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply h1; linear_combination hx + (1 - x) * h
  · intro h; apply h1; linear_combination hx - x * h
  · intro h; apply h3; linear_combination hx + (2 - x) * h
  · intro h; apply h1; linear_combination x * hx + (1 - x) * h
  · intro h; apply h2; linear_combination (-x ^ 3 - x ^ 2 + x + 2) * hx + x * h

private theorem phi12_nonzeros (hlarge : 3 < p) (x : ZMod p) (hx : x ^ 4 - x ^ 2 + 1 = 0) :
    x ≠ 0 ∧ x - 1 ≠ 0 ∧ x + 1 ≠ 0 ∧
      x ^ 2 + 1 ≠ 0 ∧ x ^ 2 - x + 1 ≠ 0 := by
  have h1 := small_ne_zero (p := p) hlarge (n := 1) (by decide) (by decide)
  have h2 := small_ne_zero (p := p) hlarge (n := 2) (by decide) (by decide)
  have h3 := small_ne_zero (p := p) hlarge (n := 3) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply h1; linear_combination hx + (-x ^ 3 + x) * h
  · intro h; apply h1; linear_combination hx + (-x ^ 3 - x ^ 2) * h
  · intro h; apply h1; linear_combination hx + (-x ^ 3 + x ^ 2) * h
  · intro h; apply h3; linear_combination hx + (2 - x ^ 2) * h
  · intro h; apply h2; linear_combination x * hx + (-x ^ 3 - x ^ 2 + x + 2) * h

theorem not_dvd_phi4_cofactor {q : ℕ} [Fact p.Prime] (hq : 1 ≤ q) (hlarge : 3 < p)
    (hd : p ∣ q ^ 2 + 1) :
    ¬ p ∣ q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 *
      (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
  have hq2 : q ≤ q ^ 2 := Nat.le_pow (by decide)
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q ^ 2 - 1 : ℤ)]
  have he := (ZMod.natCast_eq_zero_iff (q ^ 2 + 1) p).mpr hd
  push_cast at he
  obtain ⟨h0, h1, h2, h6, h12⟩ := phi4_nonzeros hlarge (q : ZMod p) he
  intro h
  have hz := (ZMod.natCast_eq_zero_iff _ p).mpr h
  push_cast [Nat.cast_sub hq, Nat.cast_sub hq2, Nat.cast_sub hq4] at hz
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (pow_ne_zero 12 h0) (pow_ne_zero 2 h1)) (pow_ne_zero 2 h2)) h6) h12) hz

theorem not_dvd_phi6_cofactor {q : ℕ} [Fact p.Prime] (hq : 1 ≤ q) (hlarge : 3 < p)
    (hd : p ∣ q ^ 2 - q + 1) :
    ¬ p ∣ q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 *
      (q ^ 2 + 1) ^ 2 * (q ^ 4 - q ^ 2 + 1) := by
  have hq2 : q ≤ q ^ 2 := Nat.le_pow (by decide)
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q ^ 2 - 1 : ℤ)]
  have he := (ZMod.natCast_eq_zero_iff (q ^ 2 - q + 1) p).mpr hd
  push_cast [Nat.cast_sub hq2] at he
  obtain ⟨h0, h1, h2, h4, h12⟩ := phi6_nonzeros hlarge (q : ZMod p) he
  intro h
  have hz := (ZMod.natCast_eq_zero_iff _ p).mpr h
  push_cast [Nat.cast_sub hq, Nat.cast_sub hq4] at hz
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (pow_ne_zero 12 h0) (pow_ne_zero 2 h1)) (pow_ne_zero 2 h2))
      (pow_ne_zero 2 h4)) h12) hz

theorem not_dvd_phi12_cofactor {q : ℕ} [Fact p.Prime] (hq : 1 ≤ q) (hlarge : 3 < p)
    (hd : p ∣ q ^ 4 - q ^ 2 + 1) :
    ¬ p ∣ q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 *
      (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) := by
  have hq2 : q ≤ q ^ 2 := Nat.le_pow (by decide)
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q ^ 2 - 1 : ℤ)]
  have he := (ZMod.natCast_eq_zero_iff (q ^ 4 - q ^ 2 + 1) p).mpr hd
  push_cast [Nat.cast_sub hq4] at he
  obtain ⟨h0, h1, h2, h4, h6⟩ := phi12_nonzeros hlarge (q : ZMod p) he
  intro h
  have hz := (ZMod.natCast_eq_zero_iff _ p).mpr h
  push_cast [Nat.cast_sub hq, Nat.cast_sub hq2] at hz
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (pow_ne_zero 12 h0) (pow_ne_zero 2 h1)) (pow_ne_zero 2 h2))
      (pow_ne_zero 2 h4)) h6) hz

private theorem parameter_relations (m : ℕ) :
    2 ^ (m + 1) ≤ 2 ^ (2 * m + 1) ∧
      (2 ^ (m + 1)) ^ 2 = 2 * 2 ^ (2 * m + 1) := by
  constructor
  · gcongr <;> omega
  · rw [← pow_mul, show (m + 1) * 2 = 2 * m + 1 + 1 by omega, pow_succ]
    ring

theorem suzuki_factorization (m : ℕ) :
    (2 ^ (2 * m + 1) - 2 ^ (m + 1) + 1) *
      (2 ^ (2 * m + 1) + 2 ^ (m + 1) + 1) = (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  obtain ⟨hle, he⟩ := parameter_relations m
  zify at he
  zify [hle]
  nlinarith

private theorem suzuki_difference (m : ℕ) :
    2 ^ (2 * m + 1) + 2 ^ (m + 1) + 1 =
      (2 ^ (2 * m + 1) - 2 ^ (m + 1) + 1) + 2 * 2 ^ (m + 1) := by
  have := (parameter_relations m).1
  omega

theorem cyclotomic_factorization (m : ℕ) :
    ReeF4.CentralCovers.OddPrimary.Cyclotomic.minusOrder m *
      ReeF4.CentralCovers.OddPrimary.Cyclotomic.plusOrder m =
        (2 ^ (2 * m + 1)) ^ 4 - (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  let q := 2 ^ (2 * m + 1)
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q ^ 2 - 1 : ℤ)]
  apply Int.natCast_inj.mp
  rw [Nat.cast_mul, ReeF4.CentralCovers.OddPrimary.Cyclotomic.minusOrder_eq,
    ReeF4.CentralCovers.OddPrimary.Cyclotomic.plusOrder_eq,
    ReeF4.CentralCovers.OddPrimary.Cyclotomic.torusOrder_cast,
    ReeF4.CentralCovers.OddPrimary.Cyclotomic.torusOrder_cast,
    ReeF4.CentralCovers.OddPrimary.Cyclotomic.orderPolynomial_mul_neg]
  rw [Nat.cast_add, Nat.cast_sub hq4]
  dsimp [q]
  rw [show (2 : ℤ) ^ (2 * m + 1) = 2 * (2 ^ m) ^ 2 by
    rw [pow_succ, Nat.mul_comm 2 m, pow_mul]; ring]

private theorem cyclotomic_difference (m : ℕ) :
    ReeF4.CentralCovers.OddPrimary.Cyclotomic.plusOrder m =
      ReeF4.CentralCovers.OddPrimary.Cyclotomic.minusOrder m +
        2 * 2 ^ (m + 1) * (2 ^ (2 * m + 1) + 1) := by
  apply Int.natCast_inj.mp
  rw [Nat.cast_add, ReeF4.CentralCovers.OddPrimary.Cyclotomic.minusOrder_eq,
    ReeF4.CentralCovers.OddPrimary.Cyclotomic.plusOrder_eq,
    ReeF4.CentralCovers.OddPrimary.Cyclotomic.torusOrder_cast,
    ReeF4.CentralCovers.OddPrimary.Cyclotomic.torusOrder_cast]
  push_cast
  rw [show (2 : ℤ) ^ (2 * m + 1) = 2 * (2 ^ m) ^ 2 by
    rw [pow_succ, Nat.mul_comm 2 m, pow_mul]; ring,
    show (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m by rw [pow_succ]; ring]
  unfold ReeF4.CentralCovers.OddPrimary.Cyclotomic.orderPolynomial
  ring

theorem suzuki_not_both {m p : ℕ} [Fact p.Prime] (hlarge : 3 < p) :
    ¬ (p ∣ 2 ^ (2 * m + 1) - 2 ^ (m + 1) + 1 ∧
      p ∣ 2 ^ (2 * m + 1) + 2 ^ (m + 1) + 1) := by
  rintro ⟨ha, hb⟩
  rw [suzuki_difference] at hb
  have ht := (Nat.dvd_add_right ha).mp hb
  have h2 : p ∣ 2 := by
    rcases (Fact.out : p.Prime).dvd_mul.mp ht with h | h
    · exact h
    · exact (Fact.out : p.Prime).dvd_of_dvd_pow h
  have := Nat.le_of_dvd (by decide : 0 < 2) h2
  omega

theorem cyclotomic_not_both {m p : ℕ} [Fact p.Prime] (hlarge : 3 < p) :
    ¬ (p ∣ ReeF4.CentralCovers.OddPrimary.Cyclotomic.minusOrder m ∧
      p ∣ ReeF4.CentralCovers.OddPrimary.Cyclotomic.plusOrder m) := by
  rintro ⟨ha, hb⟩
  have hf : p ∣ (2 ^ (2 * m + 1)) ^ 4 - (2 ^ (2 * m + 1)) ^ 2 + 1 := by
    rw [← cyclotomic_factorization]
    exact dvd_mul_of_dvd_left ha _
  rw [cyclotomic_difference] at hb
  have ht := (Nat.dvd_add_right ha).mp hb
  have hn : ¬ p ∣ 2 * 2 ^ (m + 1) := by
    intro h
    have h2 : p ∣ 2 := by
      rcases (Fact.out : p.Prime).dvd_mul.mp h with h | h
      · exact h
      · exact (Fact.out : p.Prime).dvd_of_dvd_pow h
    have := Nat.le_of_dvd (by decide : 0 < 2) h2
    omega
  have hplus := ((Fact.out : p.Prime).dvd_mul.mp ht).resolve_left hn
  let q := 2 ^ (2 * m + 1)
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q ^ 2 - 1 : ℤ)]
  have hz := (ZMod.natCast_eq_zero_iff _ p).mpr hf
  change ((q ^ 4 - q ^ 2 + 1 : ℕ) : ZMod p) = 0 at hz
  push_cast [Nat.cast_sub hq4] at hz
  have he := (ZMod.natCast_eq_zero_iff _ p).mpr hplus
  change ((q + 1 : ℕ) : ZMod p) = 0 at he
  push_cast at he
  exact (phi12_nonzeros hlarge (q : ZMod p) hz).2.2.1 he
end ReeF4.CentralCovers.OddPrimary.GoodPrimeArithmetic
