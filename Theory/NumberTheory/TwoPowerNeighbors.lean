module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Fermat

/-!
# Prime neighbors of powers of two

A nonzero integer with no odd prime divisor is a power of two. If r is
an odd prime, applying this to r-1 gives r = 2^(2^k)+1. Applying it to
r+1 gives r+1 = 2^b with b prime. The cases r=3 (k=0 or b=2) are
included, and zero is excluded before extracting prime divisors.

Source application: the Fermat and Mersenne restrictions in
Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17, p.39.
-/

@[expose] public section

namespace Nat

theorem eq_two_pow_of_no_odd_prime_dvd {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ n) : ∃ a : ℕ, n = 2 ^ a := by
  obtain ⟨a, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 2 (by decide)
  have hmone : m = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hne
    have hpne : p ≠ 2 := fun heq => hm (heq ▸ hpm)
    apply h p hp hpne
    rw [he]
    exact dvd_mul_of_dvd_right hpm _
  exact ⟨a, by simpa only [hmone, mul_one] using he⟩

theorem fermat_of_no_odd_prime_dvd_pred {r : ℕ} (hr : r.Prime) (ho : r ≠ 2)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ r - 1) :
    ∃ k : ℕ, r = 2 ^ (2 ^ k) + 1 := by
  obtain ⟨a, ha⟩ := eq_two_pow_of_no_odd_prime_dvd (n := r - 1)
    (by have := hr.two_le; omega) h
  have hra : r = 2 ^ a + 1 := by have := hr.two_le; omega
  have ha0 : a ≠ 0 := by intro h0; simp [h0] at hra; exact ho hra
  have hprime : (2 ^ a + 1).Prime := hra ▸ hr
  obtain ⟨k, hk⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < 2) ha0 hprime
  exact ⟨k, hk ▸ hra⟩

theorem mersenne_of_no_odd_prime_dvd_succ {r : ℕ} (hr : r.Prime)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ r + 1) :
    ∃ b : ℕ, b.Prime ∧ r + 1 = 2 ^ b := by
  obtain ⟨b, hb⟩ := eq_two_pow_of_no_odd_prime_dvd (n := r + 1) (by omega) h
  have hb1 : b ≠ 1 := by intro h1; simp [h1] at hb; have := hr.two_le; omega
  have he : r = 2 ^ b - 1 := by omega
  exact ⟨b, (Nat.prime_of_pow_sub_one_prime hb1 (he ▸ hr)).2, hb⟩
end Nat
