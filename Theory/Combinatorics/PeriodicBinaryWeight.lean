module

public import Theory.Combinatorics.PeriodicDigitProduct

/-!
# Single nonzero digits in a periodic binary weight

Suppose a weight below `2^(s*t)` has period `s`, expressed by
`(2^(s*t)-1) ∣ w*(2^s-1)`. If its binary digit product is `2^t`,
then each repeated block has exactly one nonzero digit. Thus the weight
is `2^j * (1 + 2^s + ... + 2^(s*(t-1)))`, with `j < s`.

Cancel the geometric sum from the period divisibility to obtain the
repeated block. Digit products multiply on concatenation; the block's
product is two, which characterizes powers of two by division by two.
The concatenation calculation follows `PeriodicDigitProduct`, retaining
its actual block instead of only the product of its digits.

This is the combinatorial support calculation for binary SL₂ tensor
parameters: GLS, volume 3, §§2.8.6, 2.8.8 and 2.8.10(b).
-/

namespace Nat
private def binaryDigitProd (k n : ℕ) : ℕ :=
  ∏ i : Fin k, (n / 2 ^ (i : ℕ) % 2 + 1)

private theorem binaryDigitProd_zero (n : ℕ) : binaryDigitProd 0 n = 1 := by
  simp [binaryDigitProd]

private theorem binaryDigitProd_succ (k n : ℕ) :
    binaryDigitProd (k + 1) n = (n % 2 + 1) * binaryDigitProd k (n / 2) := by
  rw [binaryDigitProd, Fin.prod_univ_succ]
  simp only [Fin.val_zero, pow_zero, Nat.div_one]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul, mul_comm]

private theorem binaryDigitProd_eq_one (k n : ℕ) (hn : n < 2 ^ k)
    (h : binaryDigitProd k n = 1) : n = 0 := by
  induction k generalizing n with
  | zero => simpa using hn
  | succ k ih =>
    rw [binaryDigitProd_succ] at h
    have hp : 0 < binaryDigitProd k (n / 2) :=
      Finset.prod_pos (fun _ _ => Nat.zero_lt_succ _)
    have hle := Nat.le_mul_of_pos_left (binaryDigitProd k (n / 2))
      (Nat.zero_lt_succ (n % 2))
    rw [h] at hle
    have hh : n % 2 + 1 = 1 ∧ binaryDigitProd k (n / 2) = 1 := by
      have hq : binaryDigitProd k (n / 2) = 1 := by omega
      exact ⟨by simpa [hq] using h, hq⟩
    have hn' : n / 2 < 2 ^ k := Nat.div_lt_of_lt_mul (by simpa [pow_succ, mul_comm] using hn)
    have hz := ih (n / 2) hn' hh.2
    omega

private theorem binaryDigitProd_eq_two (k n : ℕ) (hn : n < 2 ^ k)
    (h : binaryDigitProd k n = 2) : ∃ j < k, n = 2 ^ j := by
  induction k generalizing n with
  | zero => simp [binaryDigitProd_zero] at h
  | succ k ih =>
    rw [binaryDigitProd_succ] at h
    have hn' : n / 2 < 2 ^ k := Nat.div_lt_of_lt_mul (by simpa [pow_succ, mul_comm] using hn)
    by_cases hr : n % 2 = 0
    · have hq : binaryDigitProd k (n / 2) = 2 := by simpa [hr] using h
      obtain ⟨j, hj, he⟩ := ih (n / 2) hn' hq
      refine ⟨j + 1, by omega, ?_⟩
      rw [pow_succ]
      omega
    · have hr1 : n % 2 = 1 := by omega
      have hq : binaryDigitProd k (n / 2) = 1 := by rw [hr1] at h; omega
      have hz := binaryDigitProd_eq_one k (n / 2) hn' hq
      exact ⟨0, by omega, by simp; omega⟩

private theorem binaryDigitProd_append (s k a b : ℕ) (ha : a < 2 ^ s) :
    binaryDigitProd (s + k) (a + 2 ^ s * b) =
      binaryDigitProd s a * binaryDigitProd k b := by
  induction s generalizing a with
  | zero =>
    have h : a = 0 := by simpa using ha
    simp [h, binaryDigitProd_zero]
  | succ s ih =>
    have hdiv : a / 2 < 2 ^ s :=
      Nat.div_lt_of_lt_mul (by simpa only [pow_succ, mul_comm] using ha)
    rw [show s + 1 + k = (s + k) + 1 by omega, binaryDigitProd_succ,
      pow_succ', mul_assoc, Nat.add_mul_mod_self_left,
      Nat.add_mul_div_left _ _ (by decide : 0 < 2), ih (a / 2) hdiv,
      binaryDigitProd_succ]
    exact mul_assoc _ _ _ |>.symm

private theorem binaryDigitProd_repeat (s t a : ℕ) (ha : a < 2 ^ s) :
    binaryDigitProd (s * t) (a * ∑ i ∈ Finset.range t, (2 ^ s) ^ i) =
      binaryDigitProd s a ^ t := by
  induction t with
  | zero => simp [binaryDigitProd_zero]
  | succ t ih =>
    rw [geom_sum_succ]
    rw [show a * (2 ^ s * (∑ i ∈ Finset.range t, (2 ^ s) ^ i) + 1) =
      a + 2 ^ s * (a * ∑ i ∈ Finset.range t, (2 ^ s) ^ i) by ring]
    rw [show s * (t + 1) = s + s * t by ring,
      binaryDigitProd_append s (s * t) a _ ha, ih, pow_succ']

/-- A periodic binary weight of absolute degree `2^t` has one nonzero
bit in each period block. The actual bit position is retained. -/
public theorem binary_weight_of_period_and_degree (s t w : ℕ)
    (hs : 0 < s) (ht : 0 < t) (hw : w < 2 ^ (s * t))
    (hperiod : 2 ^ (s * t) - 1 ∣ w * (2 ^ s - 1))
    (hd : (∏ i : Fin (s * t), (w / 2 ^ (i : ℕ) % 2 + 1)) = 2 ^ t) :
    ∃ j < s, w = 2 ^ j * ∑ i ∈ Finset.range t, (2 ^ s) ^ i := by
  let R := ∑ i ∈ Finset.range t, (2 ^ s) ^ i
  have hP : 1 < 2 ^ s := one_lt_pow₀ (by decide) hs.ne'
  have hRpos : 0 < R := by
    apply Finset.sum_pos'
    · intro i _; exact Nat.zero_le _
    · exact ⟨0, Finset.mem_range.mpr ht, by simp⟩
  have hgeom : R * (2 ^ s - 1) = 2 ^ (s * t) - 1 := by
    simpa only [R, pow_mul] using geom_sum_mul_of_one_le hP.le t
  have hdiv : R ∣ w := by
    apply Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < 2 ^ s - 1)
    rwa [hgeom]
  obtain ⟨a, ha⟩ := hdiv
  have halt : a < 2 ^ s := by
    have hle : R * a ≤ R * (2 ^ s - 1) := by rw [← ha, hgeom]; omega
    have := Nat.le_of_mul_le_mul_left hle hRpos
    omega
  have hpow : binaryDigitProd s a ^ t = 2 ^ t := by
    rw [← binaryDigitProd_repeat s t a halt, ← mul_comm R a, ← ha]
    exact hd
  have hd2 : binaryDigitProd s a = 2 := (Nat.pow_left_inj ht.ne').mp hpow
  obtain ⟨j, hj, rfl⟩ := binaryDigitProd_eq_two s a halt hd2
  exact ⟨j, hj, ha.trans (mul_comm _ _)⟩
end Nat
