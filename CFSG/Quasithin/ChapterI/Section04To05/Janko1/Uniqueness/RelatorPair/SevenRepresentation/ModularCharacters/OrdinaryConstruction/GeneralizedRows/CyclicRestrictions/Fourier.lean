module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.CyclicRestrictions.Certificates
public import Mathlib.Tactic.LinearCombination

/-!
# Evaluation of the cyclic restriction certificates

The checked integer polynomial identities are evaluated at compatible
primitive roots. Prime-order moduli vanish by the geometric sum; the moduli
for 6, 10 and 15 vanish using the factorization of X^n - 1 and the nonvanishing
of the proper-order factors. Thus the literal table on each generator power
is the supplied integer polynomial in a linear character.

The derived numerical data retains the GPL-3.0-or-later attribution documented
in `FourierData.lean`. Source: Janko (1966), ordinary-character calculation;
Gorenstein §16.6, p.482.
-/

public section
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.CyclicRestrictions
open CyclicCharacterPolynomial


private theorem valuePolynomial_eval_0 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 0 j) z = ordinaryValue (z ^ (n / 5)) z 0 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_1 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 1 j) z = ordinaryValue (z ^ (n / 5)) z 1 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_2 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 2 j) z = ordinaryValue (z ^ (n / 5)) z 2 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_3 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 3 j) z = ordinaryValue (z ^ (n / 5)) z 3 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_4 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 4 j) z = ordinaryValue (z ^ (n / 5)) z 4 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_5 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 5 j) z = ordinaryValue (z ^ (n / 5)) z 5 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_6 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 6 j) z = ordinaryValue (z ^ (n / 5)) z 6 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_7 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 7 j) z = ordinaryValue (z ^ (n / 5)) z 7 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_8 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 8 j) z = ordinaryValue (z ^ (n / 5)) z 8 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_9 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 9 j) z = ordinaryValue (z ^ (n / 5)) z 9 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_10 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 10 j) z = ordinaryValue (z ^ (n / 5)) z 10 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_11 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 11 j) z = ordinaryValue (z ^ (n / 5)) z 11 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_12 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 12 j) z = ordinaryValue (z ^ (n / 5)) z 12 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_13 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 13 j) z = ordinaryValue (z ^ (n / 5)) z 13 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

private theorem valuePolynomial_eval_14 (n : ℕ) (j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n 14 j) z = ordinaryValue (z ^ (n / 5)) z 14 j := by
  fin_cases j <;>
    simp [valuePolynomial, ordinaryValue, eval, ← pow_mul, Nat.mul_comm]

theorem valuePolynomial_eval (n : ℕ) (i j : Fin 15) (z : ℂ) :
    eval (valuePolynomial n i j) z = ordinaryValue (z ^ (n / 5)) z i j := by
  fin_cases i
  · exact valuePolynomial_eval_0 n j z
  · exact valuePolynomial_eval_1 n j z
  · exact valuePolynomial_eval_2 n j z
  · exact valuePolynomial_eval_3 n j z
  · exact valuePolynomial_eval_4 n j z
  · exact valuePolynomial_eval_5 n j z
  · exact valuePolynomial_eval_6 n j z
  · exact valuePolynomial_eval_7 n j z
  · exact valuePolynomial_eval_8 n j z
  · exact valuePolynomial_eval_9 n j z
  · exact valuePolynomial_eval_10 n j z
  · exact valuePolynomial_eval_11 n j z
  · exact valuePolynomial_eval_12 n j z
  · exact valuePolynomial_eval_13 n j z
  · exact valuePolynomial_eval_14 n j z

private theorem modulus_from_factor (z : ℂ) (n a b : ℕ) (hz : IsPrimitiveRoot z n)
    (m : List ℤ) (ha : ¬ n ∣ a) (hb : ¬ n ∣ b)
    (hfactor : eval m z * (z ^ a - 1) * (z ^ b - 1) = (z ^ n - 1) * (z - 1)) :
    eval m z = 0 := by
  have hza : z ^ a - 1 ≠ 0 := sub_ne_zero.mpr (mt (hz.pow_eq_one_iff_dvd a).mp ha)
  have hzb : z ^ b - 1 ≠ 0 := sub_ne_zero.mpr (mt (hz.pow_eq_one_iff_dvd b).mp hb)
  have he : eval m z * (z ^ a - 1) * (z ^ b - 1) = 0 := by
    rw [hfactor, hz.pow_eq_one]
    ring
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hzb)).resolve_right hza

theorem modulus_eval (j : Fin 15) (z : ℂ) (hz : IsPrimitiveRoot z (classOrder j)) :
    eval (modulus j) z = 0 := by
  fin_cases j
  · have h := hz.pow_eq_one
    norm_num [classOrder] at h
    simp [modulus, eval, h]
  · have hg := hz.geom_sum_eq_zero (by norm_num [classOrder])
    norm_num [classOrder, Finset.sum_range_succ] at hg
    norm_num [modulus, eval]
    linear_combination hg
  · have hg := hz.geom_sum_eq_zero (by norm_num [classOrder])
    norm_num [classOrder, Finset.sum_range_succ] at hg
    norm_num [modulus, eval]
    linear_combination hg
  · have hg := hz.geom_sum_eq_zero (by norm_num [classOrder])
    norm_num [classOrder, Finset.sum_range_succ] at hg
    norm_num [modulus, eval]
    linear_combination hg
  · have hg := hz.geom_sum_eq_zero (by norm_num [classOrder])
    norm_num [classOrder, Finset.sum_range_succ] at hg
    norm_num [modulus, eval]
    linear_combination hg
  · apply modulus_from_factor z 6 2 3 hz _ (by decide) (by decide)
    norm_num [modulus, eval]
    ring
  · have hg := hz.geom_sum_eq_zero (by norm_num [classOrder])
    norm_num [classOrder, Finset.sum_range_succ] at hg
    norm_num [modulus, eval]
    linear_combination hg
  · apply modulus_from_factor z 10 2 5 hz _ (by decide) (by decide)
    norm_num [modulus, eval]
    ring
  · apply modulus_from_factor z 10 2 5 hz _ (by decide) (by decide)
    norm_num [modulus, eval]
    ring
  · have hg := hz.geom_sum_eq_zero (by norm_num [classOrder])
    norm_num [classOrder, Finset.sum_range_succ] at hg
    norm_num [modulus, eval]
    linear_combination hg
  · apply modulus_from_factor z 15 3 5 hz _ (by decide) (by decide)
    norm_num [modulus, eval]
    ring
  · apply modulus_from_factor z 15 3 5 hz _ (by decide) (by decide)
    norm_num [modulus, eval]
    ring
  · have hg := hz.geom_sum_eq_zero (by norm_num [classOrder])
    norm_num [classOrder, Finset.sum_range_succ] at hg
    norm_num [modulus, eval]
    linear_combination hg
  · have hg := hz.geom_sum_eq_zero (by norm_num [classOrder])
    norm_num [classOrder, Finset.sum_range_succ] at hg
    norm_num [modulus, eval]
    linear_combination hg
  · have hg := hz.geom_sum_eq_zero (by norm_num [classOrder])
    norm_num [classOrder, Finset.sum_range_succ] at hg
    norm_num [modulus, eval]
    linear_combination hg

theorem fourier_identity (j i : Fin 15) (z : ℂ) (hz : IsPrimitiveRoot z (classOrder j))
    (k : Fin (classOrder j)) :
    ordinaryValue (z ^ (classOrder j / 5)) z i (ordinaryPowerClass j k) =
      eval (coefficients j i) (z ^ (k : ℕ)) := by
  have he := eval_eq_of_certificate _ _ _ _ z (modulus_eval j z hz) (certificates j i k)
  rw [valuePolynomial_eval, eval_powerImage _ _ _ _ _ hz.pow_eq_one] at he
  simpa using he

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.CyclicRestrictions
