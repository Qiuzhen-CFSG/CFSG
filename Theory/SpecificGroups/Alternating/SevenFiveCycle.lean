module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-!
# A cyclic five-subgroup with squaring automorphism in A₇

Use the five-cycle on the first five letters. Multiplication by two on its
cyclic coordinates is an odd four-cycle; multiplying by the transposition
of the two remaining letters makes its action even. Thus its full order-four
automorphism occurs inside A₇. The displayed permutations and their equations
are checked by kernel reduction.

Source application: the degree-three exclusions in the Theorem C inspection
of Aschbacher–Smith, E.6.18, combined manuscript (1 March 2004), printed p.252.
-/

namespace alternatingGroup

private def fiveCycleSeven : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4

private def squareActorSeven : Equiv.Perm (Fin 7) :=
  Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 4 3 * Equiv.swap 5 6

/-- A₇ contains an element of order five conjugated to its square. -/
public theorem exists_five_cycle_square_pair_seven :
    ∃ x y : alternatingGroup (Fin 7), orderOf x = 5 ∧ y * x * y⁻¹ = x ^ 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hxmem : fiveCycleSeven ∈ alternatingGroup (Fin 7) := by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    decide +kernel
  have hymem : squareActorSeven ∈ alternatingGroup (Fin 7) := by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    decide +kernel
  let x : alternatingGroup (Fin 7) := ⟨fiveCycleSeven, hxmem⟩
  let y : alternatingGroup (Fin 7) := ⟨squareActorSeven, hymem⟩
  refine ⟨x, y, orderOf_eq_prime ?_ ?_, ?_⟩
  · apply Subtype.ext
    change fiveCycleSeven ^ 5 = 1
    decide +kernel
  · intro h
    have hh : fiveCycleSeven = 1 := congrArg Subtype.val h
    exact (by decide +kernel : fiveCycleSeven ≠ 1) hh
  · apply Subtype.ext
    change squareActorSeven * fiveCycleSeven * squareActorSeven⁻¹ = fiveCycleSeven ^ 2
    decide +kernel

end alternatingGroup
