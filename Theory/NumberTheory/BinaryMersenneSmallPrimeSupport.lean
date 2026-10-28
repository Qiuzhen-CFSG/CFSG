module
public import Theory.NumberTheory.TwoPowerNeighbors
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum

/-!
# Binary Mersenne numbers supported on three and five

An odd prime divisor q of m would make 2^q-1 divide 2^m-1. Since q is
odd, 2^q-1 has neither three nor five as a divisor, which contradicts the
prime support hypothesis. Thus m is a power of two. If 8 divides m, the
prime 17 divides 2^m-1. For m at least two, only m=2 and m=4 remain.

Source application: the Borel parameter step in Aschbacher--Smith,
proof of 14.6.14, printed p.1033. This arithmetic lemma does not construct
the source Borel subgroup or determine the ambient automorphism action.
-/

namespace Nat

private theorem mersenne_dvd_of_dvd {m n : ℕ} (h : m ∣ n) :
    2 ^ m - 1 ∣ 2 ^ n - 1 := by
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.pow_sub_one_mod_pow_sub_one, Nat.mod_eq_zero_of_dvd h]
  simp

private theorem odd_mersenne_no_small_primes {n : ℕ} (hn : Odd n) :
    ¬ 3 ∣ 2 ^ n - 1 ∧ ¬ 5 ∣ 2 ^ n - 1 := by
  have hpos : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_pow _ _ (by decide)
  have hthree : (2 : ℕ) ^ n % 3 = 2 := by
    obtain ⟨k,rfl⟩ := hn
    norm_num [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  have hfive : ((2 : ℕ) ^ n) ^ 2 % 5 = 4 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    obtain ⟨k,rfl⟩ := hn
    norm_num [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  constructor
  · intro hd
    have he : (2 : ℕ) ^ n % 3 = 1 := by
      conv_lhs => rw [← Nat.sub_add_cancel hpos]
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
    omega
  · intro hd
    have he : (2 : ℕ) ^ n % 5 = 1 := by
      conv_lhs => rw [← Nat.sub_add_cancel hpos]
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
    rw [Nat.pow_mod,he] at hfive
    norm_num at hfive

public theorem two_pow_sub_one_small_prime_support {m : ℕ} (hm : 2 ≤ m)
    (h : ∀ q : ℕ, q.Prime → q ∣ 2 ^ m - 1 → q = 3 ∨ q = 5) :
    m = 2 ∨ m = 4 := by
  obtain ⟨a,ha⟩ := Nat.eq_two_pow_of_no_odd_prime_dvd (n := m) (by omega) (by
    intro q hq hq2 hqm
    have ho : Odd q := Nat.odd_iff.mpr (hq.eq_two_or_odd.resolve_left hq2)
    have hp : 4 ≤ (2 : ℕ) ^ q := by
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hq.two_le
    obtain ⟨r,hr,hrd⟩ := Nat.exists_prime_and_dvd (n := 2 ^ q - 1) (by omega)
    rcases h r hr (hrd.trans (mersenne_dvd_of_dvd hqm)) with rfl | rfl
    · exact (odd_mersenne_no_small_primes ho).1 hrd
    · exact (odd_mersenne_no_small_primes ho).2 hrd)
  have ha3 : a < 3 := by
    by_contra! hh
    have hd : 8 ∣ m := by
      rw [ha]
      exact pow_dvd_pow 2 hh
    have h17 : 17 ∣ 2 ^ m - 1 :=
      (by norm_num : 17 ∣ (2 : ℕ) ^ 8 - 1).trans (mersenne_dvd_of_dvd hd)
    rcases h 17 (by decide) h17 with hh | hh <;> omega
  interval_cases a <;> norm_num at ha ⊢ <;> omega

end Nat
