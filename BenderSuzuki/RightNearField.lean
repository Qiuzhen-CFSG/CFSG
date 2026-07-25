/-
Authors: OpenAI
-/

module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.TransferInstance
public import Mathlib.Algebra.Ring.Basic

/-!
# Right near-fields

This file contains the low-level algebraic definition used by Peterfalvi
Appendix II and by external finite-group classification results.
-/

namespace BenderSuzuki
namespace PFAppendixII

universe u

/-- A (right) near-field: addition is commutative, the nonzero elements form a
group, and multiplication distributes over addition in its left argument. -/
public class RightNearField (F : Type u) extends AddCommGroup F, GroupWithZero F where
  right_distrib : ∀ a b c : F, (a + b) * c = a * c + b * c

/-- In a right near-field, left multiplication by minus one is additive
negation. This uses only the distributive law available in the near-field. -/
public theorem rightNearField_neg_one_mul
    {F : Type u} [RightNearField F] (x : F) : (-1 : F) * x = -x := by
  apply eq_neg_of_add_eq_zero_right
  calc
    x + (-1 : F) * x = 1 * x + (-1 : F) * x := by rw [one_mul]
    _ = (1 + (-1 : F)) * x := (RightNearField.right_distrib 1 (-1) x).symm
    _ = 0 := by rw [add_neg_cancel, zero_mul]

/-- Minus one has multiplicative order dividing two in every right near-field. -/
public theorem rightNearField_sq_neg_one
    {F : Type u} [RightNearField F] : (-1 : F) ^ 2 = 1 := by
  rw [pow_two, rightNearField_neg_one_mul]
  simp

/-- The only roots of `x ^ 2 = 1` in a right near-field are `1` and `-1`. -/
public theorem rightNearField_eq_one_or_eq_neg_one_of_sq_eq_one
    {F : Type u} [RightNearField F] {x : F} (hx : x ^ 2 = 1) :
    x = 1 ∨ x = -1 := by
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  right
  by_contra hxneg
  have hsum : 1 + x ≠ 0 := by
    intro hzero
    exact hxneg (eq_neg_of_add_eq_zero_right hzero)
  have hmul : (1 + x) * x = (1 + x) * 1 := by
    calc
      (1 + x) * x = 1 * x + x * x := RightNearField.right_distrib 1 x x
      _ = x + 1 := by rw [one_mul, ← pow_two, hx]
      _ = 1 + x := add_comm x 1
      _ = (1 + x) * 1 := (mul_one (1 + x)).symm
  exact hx1 (mul_left_cancel₀ hsum hmul)

end PFAppendixII
end BenderSuzuki
