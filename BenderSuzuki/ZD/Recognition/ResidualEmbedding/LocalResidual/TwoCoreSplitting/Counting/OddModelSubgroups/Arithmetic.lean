module

public import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Numerical consequences of the odd-subgroup analysis

These arithmetic lemmas supply the final numerical steps of GLS, Volume 4,
Chapter 2, Lemmas 17.3–17.5. They are conditional on torus orders or the
unitary divisibility statement; the concrete group theory must supply those
premises separately.

For Suzuki groups, q is the matrix-field order 2^(2m+1). The correct two
nonsplit orders are q ± 2^(m+1) + 1, as stated in GLS, Volume 3,
Theorem 6.5.4 (refs/KGroup/GLS3/chapter6.tex). This resolves the garbled
square-root expression in refs/KGroup/GLS4/Chapter4.tex, Lemma 3.8.
-/

namespace BenderSuzuki.ZD

/-- The unitary index divisibility and congruence force c = q+1.
No parity hypothesis on c is needed. -/
public theorem unitary_index_eq_succ_of_dvd {q c : ℕ} (hq : 2 < q) (hc : c ≠ 1)
    (hmod : c % q = 1) (hd : c ∣ 3 * (q + 1)) : c = q + 1 := by
  have hcl : q + 1 ≤ c := by
    by_contra h
    have hle : c ≤ q := by omega
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact hc ((Nat.mod_eq_of_lt hlt).symm.trans hmod)
    · simp at hmod
  obtain ⟨k, hk⟩ := hd
  have hkpos : 0 < k := by nlinarith
  have hkbound : k ≤ 3 := by nlinarith
  have hkm : k % q = 3 % q := by
    have he := congrArg (fun x => x % q) hk
    simpa [Nat.mul_mod, Nat.add_mod, hmod, Nat.mod_eq_of_lt (show 1 < q by omega)] using he.symm
  have hk3 : k = 3 := by
    by_cases hq3 : q = 3
    · subst q
      omega
    · rw [Nat.mod_eq_of_lt (by omega : k < q), Nat.mod_eq_of_lt (by omega : 3 < q)] at hkm
      exact hkm
  subst k
  omega

/-- Among the two linear torus orders, only q+1 is congruent to 1. -/
public theorem linear_torus_order_eq_succ {q c : ℕ} (hq : 2 < q)
    (hmod : c % q = 1) (hc : c = q - 1 ∨ c = q + 1) : c = q + 1 := by
  rcases hc with rfl | hc
  · rw [Nat.mod_eq_of_lt (by omega)] at hmod
    omega
  · exact hc

/-- None of the three Suzuki torus orders is congruent to 1 modulo q. -/
public theorem suzuki_torus_order_not_congruent_one (m c : ℕ) (hm : 0 < m)
    (hc : c = 2 ^ (2 * m + 1) - 1 ∨
      c = 2 ^ (2 * m + 1) + 2 ^ (m + 1) + 1 ∨
      c = 2 ^ (2 * m + 1) - 2 ^ (m + 1) + 1) :
    c % (2 ^ (2 * m + 1)) ≠ 1 := by
  have hr : 2 ≤ (2 : ℕ) ^ m := by
    simpa using Nat.pow_le_pow_right (n := 2) (by decide) hm
  have hs : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
  have hq : (2 : ℕ) ^ (2 * m + 1) = 2 * (2 ^ m) ^ 2 := by
    rw [pow_add, Nat.mul_comm 2 m, pow_mul]
    ring
  have hsmall : 2 ^ (m + 1) + 1 < (2 : ℕ) ^ (2 * m + 1) := by rw [hq, hs]; nlinarith
  have hlarge : 2 < (2 : ℕ) ^ (2 * m + 1) := by omega
  rcases hc with rfl | rfl | rfl
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.add_assoc, Nat.add_mod_left, Nat.mod_eq_of_lt hsmall]
    omega
  · rw [Nat.mod_eq_of_lt (by rw [hs] at *; omega)]
    have : 2 ^ (m + 1) < (2 : ℕ) ^ (2 * m + 1) := by omega
    omega

end BenderSuzuki.ZD
