module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Products of repeated words

A word of period `s` has product over `s*t` entries equal to the `t`th power
of its product over the first `s` entries. The proof cuts off one period and
uses the shift identity on the remaining entries.

This elementary identity is the product step in the Frobenius descent of
tensor words (GLS3, Remark 2.8.8).
-/

public section

namespace Finset

/-- A product over whole periods is a power of the product over one period. -/
theorem prod_range_mul_of_period {M : Type*} [CommMonoid M]
    (f : ℕ → M) (s t : ℕ) (hperiod : ∀ i, f (i + s) = f i) :
    (∏ i ∈ range (s * t), f i) = (∏ i ∈ range s, f i) ^ t := by
  have hshift : (fun i => f (s + i)) = f := by
    funext i
    simpa only [Nat.add_comm] using hperiod i
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, Nat.add_comm (s * t) s, prod_range_add, hshift, ih, pow_succ']

end Finset
