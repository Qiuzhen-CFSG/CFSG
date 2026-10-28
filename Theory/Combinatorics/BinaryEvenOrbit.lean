module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# A coarse bound for even binary tensor repetition

If a positive binary tensor block repeats an even positive number of times,
the coarse inequality `s * (2^a)^t ≤ 2*s*t + 4` already forces one binary
factor per block and exactly two repetitions. Exponential growth excludes
four or more repetitions; the remaining square excludes `a ≥ 2`.

Application: the Schur-linear outer SL₂ actor in Aschbacher--Smith K.3.1,
printed pp.453--454, using the extendability argument of Guralnick--Malle,
Classification of 2F-modules II, Proposition 4.1(2), manuscript p.22.
-/

public section

namespace Nat
/-- A coarse bound and even repetition force the minimal binary pair. -/
theorem binary_even_orbit_of_coarse {s t a : ℕ} (hs : 0 < s)
    (ht : 0 < t) (ha : 0 < a) (he : Even t)
    (hd : s * (2 ^ a) ^ t ≤ 2 * (s * t) + 4) :
    a = 1 ∧ t = 2 := by
  have ht2 : 2 ≤ t := by obtain ⟨k, rfl⟩ := he; omega
  have hgrow (n : ℕ) (hn : 4 ≤ n) : 2 * n + 4 < 2 ^ n := by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih => rw [pow_succ]; omega
  have hp : 2 ^ t ≤ (2 ^ a) ^ t := by
    apply Nat.pow_le_pow_left
    exact le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) ha)
  have htlt : t < 4 := by
    by_contra h
    have hm := Nat.mul_lt_mul_of_pos_left (hgrow t (by omega)) hs
    have hh := Nat.mul_le_mul_left s hp
    nlinarith
  have htEq : t = 2 := by obtain ⟨k, hk⟩ := he; omega
  refine ⟨?_, htEq⟩
  rw [htEq] at hd
  have hs1 : 1 ≤ s := hs
  by_contra h
  have ha2 : 2 ≤ a := by omega
  have hfour : 4 ≤ 2 ^ a := (by norm_num : 4 = 2 ^ 2) ▸
    Nat.pow_le_pow_right (by decide) ha2
  nlinarith [Nat.mul_le_mul_left s (show 16 ≤ (2 ^ a) ^ 2 by nlinarith)]
end Nat
