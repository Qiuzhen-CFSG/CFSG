module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Products of periodically repeated base digits

If p≥2, s,t>0, and 0<n<p^(s*t), the divisibility
(p^(s*t)-1) | n*(p^s-1) forces the length-s base-p digit block of n
to repeat t times. Consequently the product of one plus all its digits
is b^t for some b≥2. If p and n are odd, t is odd and b is even.
Primality of the base is not required; the maximal all-(p-1) digit
string and leading zero digits are included.

Factor p^(s*t)-1 by the geometric sum in p^s and cancel the positive
factor p^s-1. The result writes n as a block a times that geometric sum,
with 0<a<p^s. A quotient/remainder induction proves the digit-product
formula for concatenated blocks, then for repetitions. The same digit
recursion proves positivity and the odd-base parity assertion. The parity
of the geometric sum identifies the parity of the number of repetitions.

This is the arithmetic period-to-dimension step following Fong--Wong
(1.15), p.149, used for the SL2 Frobenius orbit dimension. It is independent
of representation theory and all classification assumptions.
-/

namespace Nat

private def digitProd (p k n : ℕ) : ℕ := ∏ i : Fin k, (n / p ^ (i : ℕ) % p + 1)

private theorem digitProd_zero (p n : ℕ) : digitProd p 0 n = 1 := by
  simp [digitProd]

private theorem digitProd_succ (p k n : ℕ) :
    digitProd p (k + 1) n = (n % p + 1) * digitProd p k (n / p) := by
  rw [digitProd, Fin.prod_univ_succ]
  simp only [Fin.val_zero, pow_zero, Nat.div_one]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul, mul_comm]

private theorem digitProd_pos (p k n : ℕ) : 0 < digitProd p k n := by
  exact Finset.prod_pos (fun _ _ => Nat.zero_lt_succ _)

private theorem digitProd_append (p : ℕ) (hp : 0 < p) (s k a b : ℕ)
    (ha : a < p ^ s) :
    digitProd p (s + k) (a + p ^ s * b) = digitProd p s a * digitProd p k b := by
  induction s generalizing a with
  | zero =>
      have h : a = 0 := by simpa using ha
      simp [h, digitProd_zero]
  | succ s ih =>
      have hdiv : a / p < p ^ s :=
        Nat.div_lt_of_lt_mul (by simpa only [pow_succ, mul_comm] using ha)
      rw [show s + 1 + k = (s + k) + 1 by omega, digitProd_succ,
        pow_succ', mul_assoc, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hp,
        ih (a / p) hdiv, digitProd_succ]
      exact mul_assoc _ _ _ |>.symm

private theorem digitProd_ge_two (p : ℕ) (k n : ℕ)
    (hn : 0 < n) (hbound : n < p ^ k) : 2 ≤ digitProd p k n := by
  induction k generalizing n with
  | zero => simp at hbound; omega
  | succ k ih =>
      rw [digitProd_succ]
      by_cases hr : n % p = 0
      · have hdiv : 0 < n / p := by
          have h := Nat.mod_add_div n p
          rw [hr] at h
          nlinarith
        have hsmall : n / p < p ^ k :=
          Nat.div_lt_of_lt_mul (by simpa only [pow_succ, mul_comm] using hbound)
        simpa [hr] using ih (n / p) hdiv hsmall
      · have h1 : 2 ≤ n % p + 1 := by omega
        exact le_trans h1 (Nat.le_mul_of_pos_right _ (digitProd_pos p k (n / p)))

private theorem digitProd_even (p : ℕ) (hp : Odd p) (k n : ℕ)
    (hn : Odd n) (hbound : n < p ^ k) : Even (digitProd p k n) := by
  induction k generalizing n with
  | zero => simp at hbound; subst n; simp at hn
  | succ k ih =>
      rw [digitProd_succ]
      by_cases hr : Odd (n % p)
      · exact (hr.add_odd (by decide : Odd 1)).mul_right _
      · have hdiv : Odd (n / p) := by
          have h := congrArg (fun a : ℕ => a % 2) (Nat.mod_add_div n p)
          rw [Nat.add_mod, Nat.mul_mod, Nat.odd_iff.mp hp, Nat.odd_iff.mp hn] at h
          rw [Nat.odd_iff] at hr ⊢
          omega
        have hsmall : n / p < p ^ k :=
          Nat.div_lt_of_lt_mul (by simpa only [pow_succ, mul_comm] using hbound)
        exact (ih (n / p) hdiv hsmall).mul_left _

private theorem digitProd_repeat (p : ℕ) (hp : 0 < p) (s t a : ℕ)
    (ha : a < p ^ s) :
    digitProd p (s * t) (a * ∑ i ∈ Finset.range t, (p ^ s) ^ i) =
      (digitProd p s a) ^ t := by
  induction t with
  | zero => simp [digitProd_zero]
  | succ t ih =>
      rw [geom_sum_succ]
      rw [show a * (p ^ s * (∑ i ∈ Finset.range t, (p ^ s) ^ i) + 1) =
        a + p ^ s * (a * ∑ i ∈ Finset.range t, (p ^ s) ^ i) by ring]
      rw [show s * (t + 1) = s + s * t by ring, digitProd_append p hp s (s * t) a _ ha,
        ih, pow_succ']

public theorem exists_digit_product_pow_of_period (p s t n : ℕ)
    (hp : 2 ≤ p) (hs : 0 < s) (ht : 0 < t) (hn : 0 < n)
    (hbound : n < p ^ (s * t))
    (hperiod : p ^ (s * t) - 1 ∣ n * (p ^ s - 1)) :
    ∃ b : ℕ, 2 ≤ b ∧
      (∏ i : Fin (s * t), (n / p ^ (i : ℕ) % p + 1)) = b ^ t ∧
      (Odd p → Odd n → Odd t ∧ Even b) := by
  let R := ∑ i ∈ Finset.range t, (p ^ s) ^ i
  have hP : 1 < p ^ s := one_lt_pow₀ (by omega : 1 < p) (by omega : s ≠ 0)
  have hRpos : 0 < R := by
    apply Finset.sum_pos'
    · intro i _
      exact Nat.zero_le _
    · exact ⟨0, Finset.mem_range.mpr ht, by simp⟩
  have hgeom : R * (p ^ s - 1) = p ^ (s * t) - 1 := by
    simpa only [R, pow_mul] using geom_sum_mul_of_one_le hP.le t
  have hd : R ∣ n := by
    apply Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < p ^ s - 1)
    rwa [hgeom]
  obtain ⟨a, ha⟩ := hd
  have hapos : 0 < a := by rw [ha] at hn; exact (mul_pos_iff_of_pos_left hRpos).mp hn
  have halt : a < p ^ s := by
    have hle : R * a ≤ R * (p ^ s - 1) := by rw [← ha, hgeom]; omega
    have := Nat.le_of_mul_le_mul_left hle hRpos
    omega
  refine ⟨digitProd p s a, digitProd_ge_two p s a hapos halt, ?_, ?_⟩
  · change digitProd p (s * t) n = _
    rw [ha, mul_comm R a]
    exact digitProd_repeat p (by omega) s t a halt
  · intro hpodd hnodd
    rw [ha, Nat.odd_mul] at hnodd
    have hRmod : R % 2 = t % 2 := by
      dsimp [R]
      rw [Finset.sum_nat_mod]
      have hpow (i : ℕ) : (p ^ s) ^ i % 2 = 1 := Nat.odd_iff.mp ((hpodd.pow).pow)
      simp only [hpow, Finset.sum_const,
        Finset.card_range, smul_eq_mul, mul_one]
    have htodd : Odd t := by
      rw [Nat.odd_iff, ← hRmod]
      exact Nat.odd_iff.mp hnodd.1
    exact ⟨htodd, digitProd_even p hpodd s a hnodd.2 halt⟩

end Nat
