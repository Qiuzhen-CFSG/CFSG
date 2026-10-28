module

public import Theory.SpecificGroups.Janko3.Model.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Orders of the J₃ standard generators

The product relation is checked on every letter of the concrete representation.
Together with the inverse-law certificates this gives element orders 2, 3 and
19. In particular these are verified relations, not presentation axioms.

Source: ATLAS standard generators for J₃,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J3/ .
-/

namespace Sporadic.Janko3

set_option maxRecDepth 40000 in
set_option maxHeartbeats 800000 in
/-- The product of the ATLAS generators has nineteenth power one. -/
public theorem atlasAB_pow : (atlasA * atlasB) ^ 19 = 1 := by
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem ab_pow : (a * b) ^ 19 = 1 := Subtype.ext atlasAB_pow

public theorem b_ne_one : b ≠ 1 := by
  intro h
  exact a_mul_b_ne_b_mul_a (by simp [h])

public theorem ab_ne_one : a * b ≠ 1 := by
  intro h
  have hp := congrArg (fun g : Model => (g : Equiv.Perm (Fin 6156)) 0) h
  have hn : atlasAFun (atlasBFun 0) ≠ 0 := by decide +kernel
  exact hn hp

public theorem orderOf_a : orderOf a = 2 := orderOf_eq_prime a_sq a_ne_one

public theorem orderOf_b : orderOf b = 3 := orderOf_eq_prime b_cube b_ne_one

public theorem orderOf_ab : orderOf (a * b) = 19 := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  exact orderOf_eq_prime ab_pow ab_ne_one

end Sporadic.Janko3
