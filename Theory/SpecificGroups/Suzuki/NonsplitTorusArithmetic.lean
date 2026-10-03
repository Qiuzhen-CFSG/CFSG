module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# The arithmetic of the two nonsplit Suzuki tori

The normalized partition count is a sum of `(n - 1)/(k*n)`, where the
orders `n` are at least five and the normalizer indices `k` are two or four.
Its value is less than one half, so there are at most two terms. The product
of the orders rules out a single term. Both indices must then be four, and
the same identity gives the sum of the two orders. Solving the resulting
quadratic gives the two Suzuki torus orders.

This module isolates the numerical argument of Huppert--Blackburn,
*Finite Groups III*, XI.3.10(i), printed pp. 192--193.
-/

namespace BenderSuzuki.MatrixGroups

/-- Every nontrivial divisor of the nonsplit degree is at least five. -/
public theorem suzuki_nonsplit_divisor_lower_bound (m n : ℕ) (hn : 1 < n) (hd : n ∣ (2 ^ (2 * m + 1)) ^ 2 + 1) : 5 ≤ n := by
  have htwo : ((2 ^ (2 * m + 1)) ^ 2 + 1) % 2 = 1 := by
    simp [Nat.add_mod, Nat.pow_mod]
  have hthree : ((2 ^ (2 * m + 1)) ^ 2 + 1) % 3 = 2 := by
    have hpow : (2 ^ (2 * m + 1)) ^ 2 = 4 ^ (2 * m + 1) := by
      rw [← pow_mul, Nat.mul_comm (2 * m + 1) 2, pow_mul]
      norm_num
    rw [hpow]
    simp [Nat.add_mod, Nat.pow_mod]
  by_contra h
  have hcases : n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases hcases with rfl | rfl | rfl
  · have := Nat.mod_eq_zero_of_dvd hd
    omega
  · have := Nat.mod_eq_zero_of_dvd hd
    omega
  · have := Nat.mod_eq_zero_of_dvd ((by decide : 2 ∣ 4).trans hd)
    omega

private theorem nonsplit_term_lower (n k : ℕ) (hn : 5 ≤ n) (hk : k = 2 ∨ k = 4) :
    (1 : ℚ) / 5 ≤ ((n : ℚ) - 1) / (k * n) := by
  have hn' : (5 : ℚ) ≤ n := by exact_mod_cast hn
  rcases hk with rfl | rfl <;>
    apply (le_div_iff₀ (by positivity)).mpr <;> push_cast <;> linarith

/-- The normalized partition equation forces two nonsplit classes, both of
normalizer index four, with the stated sum and product of subgroup orders. -/
public theorem suzuki_nonsplit_counting_arithmetic {α : Type*} [DecidableEq α]
    (s : Finset α) (n k : α → ℕ) (q : ℕ) (hq : 8 ≤ q)
    (hn : ∀ a ∈ s, 5 ≤ n a)
    (hk : ∀ a ∈ s, k a = 2 ∨ k a = 4)
    (hprod : (∏ a ∈ s, n a) = q ^ 2 + 1)
    (hcount : (∑ a ∈ s, ((n a : ℚ) - 1) / (k a * n a)) =
      (q : ℚ) * (q - 1) / (2 * (q ^ 2 + 1))) :
    ∃ a b, a ≠ b ∧ s = {a, b} ∧ k a = 4 ∧ k b = 4 ∧
      n a * n b = q ^ 2 + 1 ∧ n a + n b = 2 * (q + 1) := by
  have hq' : (8 : ℚ) ≤ q := by exact_mod_cast hq
  have hD : (0 : ℚ) < q ^ 2 + 1 := by positivity
  have hhalf : (∑ a ∈ s, ((n a : ℚ) - 1) / (k a * n a)) < 1 / 2 := by
    rw [hcount]
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hlower := Finset.sum_le_sum (fun a ha => nonsplit_term_lower (n a) (k a) (hn a ha) (hk a ha))
  have hcard : s.card ≤ 2 := by
    have h : (s.card : ℚ) * (1 / 5) < 1 / 2 := by
      simpa using lt_of_le_of_lt hlower hhalf
    have : (s.card : ℚ) < 3 := by linarith
    have : s.card < 3 := by exact_mod_cast this
    omega
  have hcard0 : s.card ≠ 0 := by
    intro h
    have hs := Finset.card_eq_zero.mp h
    simp only [hs, Finset.prod_empty] at hprod
    nlinarith
  have hcard1 : s.card ≠ 1 := by
    intro h
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    have hna : n a = q ^ 2 + 1 := by simpa using hprod
    have hka := hk a (by simp)
    simp only [Finset.sum_singleton, hna, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hcount
    rcases hka with hka | hka <;> rw [hka] at hcount <;> norm_num at hcount
    · have heq : (q : ℚ) ^ 2 = q * (q - 1) :=
        (div_left_inj' (ne_of_gt (by positivity : (0 : ℚ) < 2 * (q ^ 2 + 1)))).mp hcount
      nlinarith
    · have heq : (q : ℚ) ^ 2 = 2 * (q * (q - 1)) := by
        field_simp at hcount
        nlinarith [hcount]
      nlinarith
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (show s.card = 2 by omega)
  have hna := hn a (by simp)
  have hnb := hn b (by simp)
  have hna' : (5 : ℚ) ≤ n a := by exact_mod_cast hna
  have hnb' : (5 : ℚ) ≤ n b := by exact_mod_cast hnb
  have hka := hk a (by simp)
  have hkb := hk b (by simp)
  simp only [Finset.sum_pair hab] at hcount hhalf
  have hfour : k a = 4 ∧ k b = 4 := by
    have hlow_a := nonsplit_term_lower (n a) (k a) hna hka
    have hlow_b := nonsplit_term_lower (n b) (k b) hnb hkb
    have htwo (t : ℕ) (ht : (5 : ℚ) ≤ t) :
        (2 : ℚ) / 5 ≤ ((t : ℚ) - 1) / (2 * t) := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    constructor
    · rcases hka with hka | hka
      · rw [hka] at hhalf
        norm_num at hhalf
        linarith [htwo (n a) hna']
      · exact hka
    · rcases hkb with hkb | hkb
      · rw [hkb] at hhalf
        norm_num at hhalf
        linarith [htwo (n b) hnb']
      · exact hkb
  have hmul : n a * n b = q ^ 2 + 1 := by simpa [Finset.prod_pair hab] using hprod
  refine ⟨a, b, hab, rfl, hfour.1, hfour.2, hmul, ?_⟩
  have hmul' : (n a : ℚ) * n b = q ^ 2 + 1 := by exact_mod_cast hmul
  rw [hfour.1, hfour.2] at hcount
  have hne_a : (n a : ℚ) ≠ 0 := by positivity
  have hne_b : (n b : ℚ) ≠ 0 := by positivity
  have hsum : (n a : ℚ) + n b = 2 * (q + 1) := by
    rw [← hmul'] at hcount
    field_simp at hcount
    norm_num at hcount
    nlinarith only [hcount, hmul']
  exact_mod_cast hsum

/-- The sum and product determine the two Suzuki orders, in either order. -/
public theorem suzuki_nonsplit_orders_of_sum_mul (m a b : ℕ)
    (hmul : a * b = (2 ^ (2 * m + 1)) ^ 2 + 1)
    (hsum : a + b = 2 * (2 ^ (2 * m + 1) + 1)) :
    (a = 2 ^ (2 * m + 1) + 2 * 2 ^ m + 1 ∧
      b = 2 ^ (2 * m + 1) - 2 * 2 ^ m + 1) ∨
    (b = 2 ^ (2 * m + 1) + 2 * 2 ^ m + 1 ∧
      a = 2 ^ (2 * m + 1) - 2 * 2 ^ m + 1) := by
  have hq : 2 ^ (2 * m + 1) = 2 * (2 ^ m) ^ 2 := by
    rw [pow_add, Nat.mul_comm 2 m, pow_mul]
    ring
  have hr : 1 ≤ (2 : ℕ) ^ m := Nat.one_le_pow m 2 (by decide)
  have hle : 2 * 2 ^ m ≤ 2 ^ (2 * m + 1) := by rw [hq]; nlinarith
  have hsub : 2 ^ (2 * m + 1) - 2 * 2 ^ m + 2 * 2 ^ m = 2 ^ (2 * m + 1) :=
    Nat.sub_add_cancel hle
  have hsq : ((a : ℤ) - (2 ^ (2 * m + 1) + 1 + 2 * 2 ^ m)) *
      (a - (2 ^ (2 * m + 1) + 1 - 2 * 2 ^ m)) = 0 := by
    have hmul' : (a : ℤ) * b = (2 ^ (2 * m + 1)) ^ 2 + 1 := by exact_mod_cast hmul
    have hsum' : (a : ℤ) + b = 2 * (2 ^ (2 * m + 1) + 1) := by exact_mod_cast hsum
    have hq' : (2 : ℤ) ^ (2 * m + 1) = 2 * (2 ^ m) ^ 2 := by exact_mod_cast hq
    nlinarith
  rcases mul_eq_zero.mp hsq with ha | ha
  · left
    have ha' : a = 2 ^ (2 * m + 1) + 2 * 2 ^ m + 1 := by
      have : (a : ℤ) = 2 ^ (2 * m + 1) + 2 * 2 ^ m + 1 := by linarith
      exact_mod_cast this
    exact ⟨ha', by omega⟩
  · right
    have ha' : a + 2 * 2 ^ m = 2 ^ (2 * m + 1) + 1 := by
      have : (a : ℤ) + 2 * 2 ^ m = 2 ^ (2 * m + 1) + 1 := by linarith
      exact_mod_cast this
    constructor <;> omega

end BenderSuzuki.MatrixGroups
