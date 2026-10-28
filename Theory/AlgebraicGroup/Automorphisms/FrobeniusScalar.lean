module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Theory.AlgebraicGroup.Automorphisms.Steinberg

/-!
# Frobenius scalars in positive characteristic

For an algebraically closed field of nonzero characteristic, this module
constructs the integral Frobenius scalar system used by the automorphism
classification.  Positive characteristic makes `ringChar k` prime, while
algebraic closedness makes the field perfect.  Thus Mathlib's Frobenius ring
equivalence is available.

The scalar at an integer `a` is the `a`-th integer power of that equivalence.
The integer-power addition law gives composition and exponent zero gives the
identity.  At natural exponents, `iterateFrobeniusEquiv_eq_pow` identifies this
power with Mathlib's iterated Frobenius, whose defining formula is
`x ↦ x ^ (ringChar k ^ a)`.

This is the scalar-field input for the Frobenius construction in GLS3,
Chapter 1, Theorem 1.15.4(a); extending it through Chevalley generators is a
separate geometric step.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The integral Frobenius scalar system of an algebraically closed field of
positive characteristic. -/
public noncomputable def frobeniusScalarSystem (hchar : ringChar k ≠ 0) :
    FrobeniusScalarSystem (k := k) (ringChar k) := by
  letI : Fact (ringChar k).Prime :=
    ⟨(CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hchar⟩
  refine
    { scalar := fun a => frobeniusEquiv k (ringChar k) ^ a
      zero := by
        rw [zpow_zero]
        rfl
      add := by
        intro a b x
        rw [zpow_add]
        rfl
      nonnegative := by
        intro a x
        rw [zpow_natCast]
        rw [← iterateFrobeniusEquiv_eq_pow]
        exact iterateFrobeniusEquiv_def k (ringChar k) a x }

end Theory.AlgebraicGroup
