module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic

/-!
# Element orders in SL₃(2)

Every determinant-one binary matrix of degree three has order dividing
three, four, or seven. The finite calculation enumerates the 512 binary
matrices, filters by determinant one, and checks these powers in the kernel.
This provides an obstruction to surjections onto groups containing elements
whose orders divide none of these three numbers.
-/

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The possible nonidentity element orders in SL₃(2) are 2, 3, 4 and 7. -/
public theorem Matrix.PSL3Two.pow_three_or_four_or_seven
    (a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    a ^ 3 = 1 ∨ a ^ 4 = 1 ∨ a ^ 7 = 1 := by
  have h : ∀ a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      a ^ 3 = 1 ∨ a ^ 4 = 1 ∨ a ^ 7 = 1 := by decide +kernel
  exact h a
