module

public import Mathlib.Data.Nat.Factors
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.SplitIfs

/-!
# Odd primes in binary signed torus orders

For n > 3 both 2ⁿ − 1 and 2ⁿ + 1 have a prime divisor greater than three.
The minus case follows modulo eight. In the plus case, an alleged power
of three has even exponent; factoring the difference of two squares makes
two powers of two differ by two, forcing 2ⁿ ≤ 8. Division by three retains
these primes and oddness when the signed congruence holds.

Source: the arithmetic step of Aschbacher–Smith 16.4.8, combined manuscript
of 1 March 2004, printed p.1188. These lemmas do not assert a group action
or infer residual generation from the torus order.
-/

public section
namespace Nat.BinarySignedTorus

private theorem three_pow_mod_eight (k : ℕ) :
    3 ^ k % 8 = if k % 2 = 0 then 1 else 3 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs with hk hs hs <;> omega

private theorem two_pow_sub_one_ne_three_pow {n : ℕ} (hn : 3 ≤ n) (k : ℕ) :
    2 ^ n - 1 ≠ 3 ^ k := by
  have hq : 8 ∣ 2 ^ n := Nat.pow_dvd_pow 2 hn
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  have hm := three_pow_mod_eight k
  intro he
  have he' : 2 ^ n = 3 ^ k + 1 := by omega
  have hz := Nat.mod_eq_zero_of_dvd hq
  rw [he', Nat.add_mod] at hz
  split_ifs at hm <;> omega

private theorem two_pow_add_one_ne_three_pow {n : ℕ} (hn : 3 < n) (k : ℕ) :
    2 ^ n + 1 ≠ 3 ^ k := by
  have hq : 8 ∣ 2 ^ n := Nat.pow_dvd_pow (m := 3) (n := n) 2 (by omega)
  have hq16 : 16 ≤ 2 ^ n := Nat.pow_le_pow_right (n := 2) (i := 4) (j := n) (by decide) (by omega)
  intro he
  have hm := three_pow_mod_eight k
  have hz := Nat.mod_eq_zero_of_dvd hq
  have hk : k % 2 = 0 := by
    have hmod := congrArg (fun a : ℕ => a % 8) he
    rw [Nat.add_mod, hz] at hmod
    split_ifs at hm <;> omega
  obtain ⟨j, hj⟩ := (Nat.even_iff.mpr hk)
  have he' : 2 ^ n + 1 = (3 ^ j) ^ 2 := by
    rw [he, hj, pow_add, pow_two]
  have hs : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by decide)
  have hs' := Nat.sub_add_cancel hs
  have hprod : (3 ^ j - 1) * (3 ^ j + 1) = 2 ^ n := by nlinarith
  obtain ⟨a, ha, hea⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show 3 ^ j - 1 ∣ 2 ^ n by rw [← hprod]; exact dvd_mul_right _ _)
  obtain ⟨b, hb, heb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show 3 ^ j + 1 ∣ 2 ^ n by rw [← hprod]; exact dvd_mul_left _ _)
  have hab : a ≤ b := by
    by_contra hh
    have := Nat.pow_lt_pow_right (by decide : 1 < 2) (show b < a by omega)
    omega
  have hd : 2 ^ a ∣ 2 := by
    have h := Nat.dvd_sub (Nat.pow_dvd_pow 2 hab) (dvd_refl (2 ^ a))
    have hdiff : 2 ^ b - 2 ^ a = 2 := by omega
    rwa [hdiff] at h
  have small : 2 ^ a = 1 ∨ 2 ^ a = 2 := (Nat.dvd_prime Nat.prime_two).mp hd
  rcases small with ha1 | ha2 <;> nlinarith

/-- A binary minus torus has a prime divisor greater than three. -/
theorem exists_prime_gt_three_dvd_sub {n : ℕ} (hn : 3 < n) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ n - 1 := by
  by_contra h
  push Not at h
  have hp : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  have he := Nat.eq_prime_pow_of_unique_prime_dvd (show 2 ^ n - 1 ≠ 0 by omega)
    (p := 3) (fun {p} hprime hd => by
      have hle := h p hprime
      have h2 : p ≠ 2 := by
        intro he
        subst p
        have hq : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
        have hqmod := Nat.mod_eq_zero_of_dvd hq
        have hmod := Nat.mod_eq_zero_of_dvd hd
        omega
      have hp2 := hprime.two_le
      by_contra hp3
      exact hle (by omega) hd)
  exact two_pow_sub_one_ne_three_pow (by omega) _ he

/-- A binary plus torus has a prime divisor greater than three after n = 3. -/
theorem exists_prime_gt_three_dvd_add {n : ℕ} (hn : 3 < n) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ n + 1 := by
  by_contra h
  push Not at h
  have he := Nat.eq_prime_pow_of_unique_prime_dvd (show (2 : ℕ) ^ n + 1 ≠ 0 by positivity)
    (p := 3) (fun {p} hprime hd => by
      have hle := h p hprime
      have h2 : p ≠ 2 := by
        intro he
        subst p
        have hq : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
        have hqmod := Nat.mod_eq_zero_of_dvd hq
        have hmod := Nat.mod_eq_zero_of_dvd hd
        omega
      have hp2 := hprime.two_le
      by_contra hp3
      exact hle (by omega) hd)
  exact two_pow_add_one_ne_three_pow hn _ he

private theorem prime_dvd_div_three {m p : ℕ} (h3 : 3 ∣ m)
    (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ m) : p ∣ m / 3 := by
  rw [← Nat.div_mul_cancel h3] at hd
  refine (hp.dvd_mul.mp hd).resolve_right ?_
  intro hd3
  have := Nat.le_of_dvd (by decide : 0 < 3) hd3
  omega

/-- The exact linear quotient order (2ⁿ − 1)/3 is odd and has a prime
factor greater than three, under the source congruence. -/
theorem linear_quotient {n : ℕ} (hn : 3 < n) (hmod : 2 ^ n % 3 = 1) :
    Odd ((2 ^ n - 1) / 3) ∧
      ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ (2 ^ n - 1) / 3 := by
  have hpos : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  have h3 : 3 ∣ 2 ^ n - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hodd : Odd (2 ^ n - 1) := by
    rw [Nat.odd_iff]
    have := Nat.mod_eq_zero_of_dvd h2
    omega
  obtain ⟨p, hp, hp3, hd⟩ := exists_prime_gt_three_dvd_sub hn
  exact ⟨hodd.of_dvd_nat (Nat.div_dvd_of_dvd h3),
    p, hp, hp3, prime_dvd_div_three h3 hp hp3 hd⟩

/-- The exact unitary quotient order (2ⁿ + 1)/3 is odd and has a prime
factor greater than three, under the source congruence. -/
theorem unitary_quotient {n : ℕ} (hn : 3 < n) (hmod : 2 ^ n % 3 = 2) :
    Odd ((2 ^ n + 1) / 3) ∧
      ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ (2 ^ n + 1) / 3 := by
  have h3 : 3 ∣ 2 ^ n + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hodd : Odd (2 ^ n + 1) := by
    rw [Nat.odd_iff]
    have := Nat.mod_eq_zero_of_dvd h2
    omega
  obtain ⟨p, hp, hp3, hd⟩ := exists_prime_gt_three_dvd_add hn
  exact ⟨hodd.of_dvd_nat (Nat.div_dvd_of_dvd h3),
    p, hp, hp3, prime_dvd_div_three h3 hp hp3 hd⟩

end Nat.BinarySignedTorus
