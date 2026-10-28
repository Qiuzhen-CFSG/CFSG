module

public import Theory.NumberTheory.BinarySignedTorus

/-!
# Parity and the exceptional binary torus degrees

Reduction modulo three distinguishes the split tori in odd and even field
degree. The existing prime-divisor calculation for signed binary orders
also shows that a torus of order `2^m + 1` can be a three-group only for
`m = 1` or `m = 3`. These are the degrees two and six when `m` is the
half-degree of a field involution.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. These are arithmetic
facts; identifying a torus action with a field involution is a separate input.
-/

public section
namespace Nat.BinaryTorusParity

theorem two_pow_mod_three (n : ℕ) :
    2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs with hn hs hs <;> omega

/-- Split tori have three-prime order in odd field degree. -/
theorem coprime_three_sub_one {n : ℕ} (hn : Odd n) :
    Nat.Coprime 3 (2 ^ n - 1) := by
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  have hm := two_pow_mod_three n
  have ho := Nat.odd_iff.mp hn
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  simp only [ho, show ¬ (1 : ℕ) = 0 by decide, if_false] at hm
  intro hd
  have := Nat.mod_eq_zero_of_dvd hd
  omega

/-- The split torus has a factor three exactly in even field degree. -/
theorem three_dvd_sub_one_iff (n : ℕ) :
    3 ∣ 2 ^ n - 1 ↔ Even n := by
  rw [Nat.even_iff, Nat.dvd_iff_mod_eq_zero]
  have hm := two_pow_mod_three n
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  split_ifs at hm <;> omega

/-- A plus torus which is a power of three has half-degree one or three. -/
theorem plus_three_power_degree {m k : ℕ} (hm : 0 < m)
    (h : 2 ^ m + 1 = 3 ^ k) : m = 1 ∨ m = 3 := by
  have hle : m ≤ 3 := by
    by_contra hle
    obtain ⟨p, hp, hp3, hd⟩ := BinarySignedTorus.exists_prime_gt_three_dvd_add
      (show 3 < m by omega)
    rw [h] at hd
    have := Nat.le_of_dvd (by decide : 0 < 3) (hp.dvd_of_dvd_pow hd)
    omega
  have hne : m ≠ 2 := by
    intro he
    subst m
    have hd : 5 ∣ 3 ^ k := by rw [← h]; norm_num
    have hd3 := Nat.prime_five.dvd_of_dvd_pow hd
    norm_num at hd3
  omega

/-- The numerical exceptional degrees for a field involution are two and six. -/
theorem field_involution_degree {n m k : ℕ} (hn : n = 2 * m) (hm : 0 < m)
    (h : 2 ^ m + 1 = 3 ^ k) : n = 2 ∨ n = 6 := by
  rcases plus_three_power_degree hm h with h | h <;> omega

end Nat.BinaryTorusParity
