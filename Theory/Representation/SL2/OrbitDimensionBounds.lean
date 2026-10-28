module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Numerical bounds for SL2 Frobenius-orbit dimensions

Fong--Wong (1E), article p.149, writes the extension exponent as `s*t` and
an irreducible prime-field dimension as `s*b^t`, where `b` is the product of
one period of the restricted-weight factors `k_i+1`. Nontriviality gives
`b ≥ 2`. For a faithful constituent, the period repetition `t` is odd and
`b` is even. These hypotheses give the lower bound `2*s*t` and the alternatives
`2*s*t`, `8*s*t/3` (with `3 ∣ s*t`), or at least `4*s*t`.

The proof uses `2*t ≤ 2^t`, and `4*t ≤ 2^t` for `t ≥ 4`. Below the larger
bound only `t=1` or `t=3` remains; parity and the bound force `b=2`.
The exceptional equality is expressed without division as `3*d=8*n`.
If `s>0`, equality in the lower bound forces `t=1` and `b=2`: the
large-period bound excludes `t≥4`, and `b³≥8` excludes `t=3`.
This identifies the Schur degree in the minimal faithful dimension case.

This module proves only the numerical step in the printed proof. Deriving
these parameters from an actual SL2 representation requires the separate
restricted-weight classification and Frobenius-descent theorems.
-/

namespace Representation.SL2

private theorem two_mul_le_two_pow {t : ℕ} (ht : 1 ≤ t) : 2 * t ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ]
    nlinarith

private theorem four_mul_le_two_pow {t : ℕ} (ht : 4 ≤ t) : 4 * t ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ]
    nlinarith

/-- Every nontrivial orbit dimension is at least twice the extension exponent. -/
public theorem orbit_dimension_lower_bound {s t b : ℕ} (ht : 0 < t) (hb : 2 ≤ b) :
    2 * (s * t) ≤ s * b ^ t := by
  have hpow := (two_mul_le_two_pow ht).trans (Nat.pow_le_pow_left hb t)
  calc
    2 * (s * t) = s * (2 * t) := by ring
    _ ≤ s * b ^ t := Nat.mul_le_mul_left s hpow

/-- Faithful-orbit parity gives exactly the three numerical alternatives in (1E). -/
public theorem orbit_dimension_trichotomy {s t b : ℕ}
    (ht : Odd t) (hb : 2 ≤ b) (hbeven : Even b) :
    s * b ^ t = 2 * (s * t) ∨
      (3 * (s * b ^ t) = 8 * (s * t) ∧ 3 ∣ s * t) ∨
      4 * (s * t) ≤ s * b ^ t := by
  by_cases hlarge : 4 * (s * t) ≤ s * b ^ t
  · exact Or.inr (Or.inr hlarge)
  have hsmall : b ^ t < 4 * t := by nlinarith
  have htlt : t < 4 := by
    by_contra h
    have := (four_mul_le_two_pow (by omega : 4 ≤ t)).trans (Nat.pow_le_pow_left hb t)
    omega
  have ht13 : t = 1 ∨ t = 3 := by obtain ⟨k, hk⟩ := ht; omega
  rcases ht13 with rfl | rfl
  · simp only [pow_one] at hsmall ⊢
    have hb2 : b = 2 := by obtain ⟨k, hk⟩ := hbeven; omega
    left
    rw [hb2]
    ring
  · have hb2 : b = 2 := by
      by_contra h
      have hb3 : 3 ≤ b := by omega
      have hpow := Nat.pow_le_pow_left hb3 3
      norm_num at hpow
      omega
    right; left
    constructor
    · rw [hb2]; ring
    · exact dvd_mul_left 3 s

/-- Equality in the faithful orbit lower bound forces a single block of size two. -/
public theorem orbit_dimension_minimal_parameters {s t b : ℕ}
    (hs : 0 < s) (ht : Odd t) (hb : 2 ≤ b)
    (heq : s * b ^ t = 2 * (s * t)) : t = 1 ∧ b = 2 := by
  have hpow : b ^ t = 2 * t := by nlinarith
  have htlt : t < 4 := by
    by_contra h
    have hbound := (four_mul_le_two_pow (by omega : 4 ≤ t)).trans
      (Nat.pow_le_pow_left hb t)
    omega
  have ht13 : t = 1 ∨ t = 3 := by obtain ⟨k, hk⟩ := ht; omega
  rcases ht13 with rfl | rfl
  · simpa using hpow
  · have hbound := Nat.pow_le_pow_left hb 3
    norm_num at hpow hbound
    omega

end Representation.SL2
