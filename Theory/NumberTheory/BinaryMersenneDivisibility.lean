module

public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum

/-!
# Binary Mersenne divisors of a power of two plus one

If `m ≥ 2` and `2^m - 1` divides `2^n + 1`, then `m = 2`.
Reducing the exponent modulo `m` gives a positive residue `2^(n % m) + 1`.
For `m ≥ 3` it is strictly smaller than the modulus, a contradiction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript, 1 March 2004, Proposition 10.2.3, printed p. 745.
There this bounds the parameter of a cyclic subgroup of the odd Cartan
centralizer. The divisibility used here concerns its exponent, not merely
the order of the ambient Cartan subgroup.
-/

namespace Nat

/-- A nontrivial binary Mersenne number dividing a power of two plus one
must be `3`. -/
public theorem eq_two_of_two_pow_sub_one_dvd_two_pow_add_one {m n : ℕ} (hm : 2 ≤ m) (h : 2 ^ m - 1 ∣ 2 ^ n + 1) : m = 2 := by
  by_contra hne
  have hm3 : 3 ≤ m := by omega
  have hp : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_pow n 2 (by omega)
  have hr : 1 ≤ (2 : ℕ) ^ (n % m) := Nat.one_le_pow _ 2 (by omega)
  have heq : (2 ^ n + 1) % (2 ^ m - 1) =
      (2 ^ (n % m) + 1) % (2 ^ m - 1) := by
    calc
      _ = ((2 ^ n - 1) + 2) % (2 ^ m - 1) := by congr 1; omega
      _ = (((2 ^ n - 1) % (2 ^ m - 1)) + 2) % (2 ^ m - 1) := by simp only [Nat.add_mod, Nat.mod_mod]
      _ = ((2 ^ (n % m) - 1) + 2) % (2 ^ m - 1) := by
        rw [Nat.pow_sub_one_mod_pow_sub_one]
      _ = _ := by congr 1; omega
  have hmod := Nat.mod_eq_zero_of_dvd h
  rw [heq] at hmod
  have hrlt : n % m ≤ m - 1 := by have := Nat.mod_lt n (by omega : 0 < m); omega
  have hpow : (2 : ℕ) ^ (n % m) ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) hrlt
  have hfour : 4 ≤ (2 : ℕ) ^ (m - 1) := by
    calc
      4 = (2 : ℕ) ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hstep : (2 : ℕ) ^ m = 2 ^ (m - 1) * 2 := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  have hlt : 2 ^ (n % m) + 1 < 2 ^ m - 1 := by omega
  rw [Nat.mod_eq_of_lt hlt] at hmod
  omega

end Nat
