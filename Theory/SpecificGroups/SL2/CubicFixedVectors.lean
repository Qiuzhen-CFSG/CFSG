module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Cubic matrices on the natural plane in characteristic two

A nonzero fixed vector forces the characteristic polynomial of a
determinant-one two-by-two matrix to be (t - 1)². In characteristic two
this makes the matrix square to one, excluding order three.
No triangularization, finite-field classification or Borel placement is needed.

Source: the natural-module calculation used in Aschbacher–Smith,
proof of 15.4.20, printed p.1164.
-/

public section

open Matrix
open scoped MatrixGroups
namespace Matrix.SL2
variable {F : Type*} [Field F] [CharP F 2]
/-- A cubic determinant-one matrix in characteristic two fixes only zero. -/
lemma cubic_fixed_eq_zero (g : SL(2,F)) (hg : orderOf g = 3)
    (v : Fin 2 → F) (hv : g.val *ᵥ v = v) : v = 0 := by
  by_contra hne
  have h0 : g.val 0 0 * v 0 + g.val 0 1 * v 1 = v 0 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 0
  have h1 : g.val 1 0 * v 0 + g.val 1 1 * v 1 = v 1 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 1
  have hd : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 = 1 :=
    (det_fin_two g.val).symm.trans g.property
  have ht0 : (2 - g.val 0 0 - g.val 1 1) * v 0 = 0 := by
    linear_combination (g.val 1 1 - 1) * h0 - g.val 0 1 * h1 - v 0 * hd
  have ht1 : (2 - g.val 0 0 - g.val 1 1) * v 1 = 0 := by
    linear_combination (g.val 0 0 - 1) * h1 - g.val 1 0 * h0 - v 1 * hd
  have ht : 2 - g.val 0 0 - g.val 1 1 = 0 := by
    by_contra hn
    have hv0 := (mul_eq_zero.mp ht0).resolve_left hn
    have hv1 := (mul_eq_zero.mp ht1).resolve_left hn
    exact hne (by ext i; fin_cases i <;> assumption)
  have h2 : (2 : F) = 0 := by simpa using (CharP.cast_eq_zero F 2)
  have hdiag : g.val 1 1 = g.val 0 0 := by
    rw [h2, zero_sub, CharTwo.neg_eq, sub_eq_zero] at ht
    exact ht.symm
  have hs : g ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    change g.val * g.val = (1 : Matrix (Fin 2) (Fin 2) F)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    · simpa [hdiag, CharTwo.sub_eq_add] using hd
    · change g.val 0 0 * g.val 0 1 + g.val 0 1 * g.val 1 1 = 0
      rw [hdiag, mul_comm (g.val 0 1) (g.val 0 0), CharTwo.add_self_eq_zero]
    · simp [hdiag, mul_comm, CharTwo.add_self_eq_zero]
    · simpa [hdiag, CharTwo.sub_eq_add, mul_comm, add_comm] using hd
  have hbad : 3 ∣ 2 := hg ▸ orderOf_dvd_of_pow_eq_one hs
  norm_num at hbad
end Matrix.SL2
