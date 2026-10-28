module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic

/-!
# The natural cubic selected by the binary Singer projector

For a nontrivial binary three-dimensional actor of order dividing seven,
the vanished reciprocal projector singles out X³+X+1. The assertion is
checked on all 512 binary matrices by the Lean kernel; it does not assume
that the chosen original actor already has this characteristic polynomial.
-/

public section
namespace BinarySingerCubic
open Matrix

private theorem matrix_check : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2),
    A^7=1 → A≠1 → 1+A^3+A^5+A^6=0 → A^3+A+1=0 := by decide +kernel

/-- A nonidentity binary three-dimensional seventh root of unity with
zero reciprocal projector satisfies the marked natural cubic. -/
theorem cubic_eq_zero_of_seven_projector
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hseven : A^7=1) (hne : A≠1) (hprojector : 1+A^3+A^5+A^6=0) :
    A^3+A+1=0 := matrix_check A hseven hne hprojector

end BinarySingerCubic
