module

public import Mathlib.Data.Nat.Basic

/-!
# Balanced exhaustive checks for the Fi₂₃ certificates

A binary recursion checks a block of length `2 ^ k` at logarithmic recursion
depth. Its soundness theorem turns a kernel-checked Boolean equality into
pointwise propositions. `Enumeration` applies it to the inverse and orbit tree.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

def checkPow (f : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => f start
  | k + 1 => checkPow f start k && checkPow f (start + 2 ^ k) k

theorem checkPow_sound (f : Nat → Bool) (k start : Nat)
    (h : checkPow f start k = true) : ∀ i, start ≤ i → i < start + 2 ^ k → f i = true := by
  induction k generalizing start with
  | zero =>
    intro i hi hj
    have : i = start := Nat.le_antisymm (Nat.le_of_lt_succ (by simpa using hj)) hi
    subst i
    exact h
  | succ k ih =>
    simp only [checkPow, Bool.and_eq_true] at h
    intro i hi hj
    by_cases hm : i < start + 2 ^ k
    · exact ih start h.1 i hi hm
    · apply ih (start + 2 ^ k) h.2 i (Nat.le_of_not_gt hm)
      simpa only [Nat.pow_succ, Nat.mul_two, Nat.add_assoc] using hj

/-- Combine adjacent certified blocks without repeating their reductions. -/
theorem checkPow_join (f : Nat → Bool) (k start : Nat)
    (h₀ : checkPow f start k = true)
    (h₁ : checkPow f (start + 2 ^ k) k = true) :
    checkPow f start (k + 1) = true := by
  simp only [checkPow, h₀, h₁, Bool.and_self]

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate
