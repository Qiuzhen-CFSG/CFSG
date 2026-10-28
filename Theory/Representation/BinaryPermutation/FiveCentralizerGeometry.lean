module

public import Theory.Representation.BinaryPermutation
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.FinCases

/-!
# Three singular vectors in the binary alternating-five module

The four-dimensional module is the even-weight core on five letters. With
z = e₁₂₃₄ and v = e₁₂, the cycle (3 4 5) fixes v, and the sum of its three
translates of z is v. The singular vector a = e₁₃₄₅ is another A₅-conjugate
of z fixed by that cycle. All equalities are checked in the actual module.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, §13.6,
printed pp.926–928, using the module conventions in §B.3.
-/

@[expose] public section
namespace BinaryPermutation.FiveCentralizerGeometry
abbrev Space := core (Fin 5)
def z : Space := ⟨![1, 1, 1, 1, 0], by rw [mem_core]; decide⟩
def v : Space := ⟨![1, 1, 0, 0, 0], by rw [mem_core]; decide⟩
def a : Space := ⟨![1, 0, 1, 1, 1], by rw [mem_core]; decide⟩
def cubic : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 2 3 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
def aConjugator : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 1 4 * Equiv.swap 0 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
abbrev act (g : alternatingGroup (Fin 5)) := coreRepresentation (Fin 5) g.val

theorem cubic_pow : cubic ^ 3 = 1 := by decide +kernel
theorem cubic_fixes_v : act cubic v = v := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide

theorem cubic_fixes_a : act cubic a = a := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide

theorem orbit_sum : z + act cubic z + act (cubic ^ 2) z = v := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide

theorem conjugate_z_eq_a : act aConjugator z = a := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide
theorem z_ne_zero : z ≠ 0 := by
  intro h
  have he := congrArg (fun x : Space => x.val 0) h
  exact (by decide : (1 : ZMod 2) ≠ 0) he

theorem v_ne_zero : v ≠ 0 := by
  intro h
  have he := congrArg (fun x : Space => x.val 0) h
  exact (by decide : (1 : ZMod 2) ≠ 0) he

theorem a_ne_zero : a ≠ 0 := by
  intro h
  have he := congrArg (fun x : Space => x.val 0) h
  exact (by decide : (1 : ZMod 2) ≠ 0) he

end BinaryPermutation.FiveCentralizerGeometry
