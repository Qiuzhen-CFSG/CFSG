module

public import Theory.Mathieu.M24.Basic
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.FinCases

/-!
# Generators for the inverted Heisenberg subgroup of M₂₄

Three concrete permutations in the Witt-design group are certified by words
in its two standard generators. GAP supplies only the word data: every
permutation equality and group relation is checked by the Lean kernel.
The alphabet 0, 1, 2, 3 denotes A, A⁻¹, B, B⁻¹, respectively; words are
evaluated in reverse order to account for GAP’s right permutation action.
As usual in the ATLAS coordinates, point 24 is represented by `0 : Fin 24`.

The two cubic elements have a nonidentity commutator commuting with both,
and the third element is an involution inverting both cubic generators.
The parent module proves that they generate a Sylow three-subgroup.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, E.4.3(2), printed pp.241–242, and I.1.1–I.1.4, printed pp.407–408.
-/

namespace Sporadic.Mathieu.M24ValueBoundParabolics.ThreeModel
open scoped commutatorElement
set_option maxRecDepth 100000

@[expose] public def aPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [2,17,21] * List.formPerm [3,7,23] *
  List.formPerm [4,15,22] * List.formPerm [6,10,20] *
  List.formPerm [11,24,18] * List.formPerm [12,16,13]

@[expose] public def bPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [1,2,12] * List.formPerm [3,4,15] *
  List.formPerm [5,17,13] * List.formPerm [6,22,20] *
  List.formPerm [7,23,10] * List.formPerm [8,14,9] *
  List.formPerm [11,24,18] * List.formPerm [16,19,21]

@[expose] public def tPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [2,12] * List.formPerm [4,15] *
  List.formPerm [6,20] * List.formPerm [7,23] *
  List.formPerm [8,14] * List.formPerm [13,17] *
  List.formPerm [16,21] * List.formPerm [18,24]

private noncomputable def letter : Fin 4 → M24
  | 0 => ⟨m24GeneratorA, m24GeneratorA_mem⟩
  | 1 => ⟨m24GeneratorA, m24GeneratorA_mem⟩⁻¹
  | 2 => ⟨m24GeneratorB, m24GeneratorB_mem⟩
  | 3 => ⟨m24GeneratorB, m24GeneratorB_mem⟩⁻¹

private noncomputable def word : List (Fin 4) → M24
  | [] => 1
  | i :: w => word w * letter i

private def aWord : List (Fin 4) := [0, 3, 0, 2, 0, 3, 0, 2, 0, 3, 0, 3, 3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 0, 2, 0, 3, 0, 3, 0, 3, 0, 2, 0]

private theorem a_word : aPerm = (word aWord).val := by
  ext i
  fin_cases i <;> decide +kernel

@[expose] public noncomputable def a : M24 :=
  ⟨aPerm, by exact a_word.symm ▸ (word aWord).property⟩

private def bWord : List (Fin 4) := [3, 0, 2, 0, 2, 0, 2, 0, 3, 0, 3, 0, 2, 2, 0, 3, 0, 2, 0, 3, 0, 2, 0, 3, 0, 3, 0, 3, 0, 2, 0, 3, 0, 3, 0, 3, 0, 2, 2, 1, 2, 1, 3, 1, 2, 1, 3, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 2, 0, 2, 0, 3, 0, 2, 0, 3, 0, 2, 0, 2, 2, 1, 2, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 2, 0, 2, 1]

private theorem b_word : bPerm = (word bWord).val := by
  ext i
  fin_cases i <;> decide +kernel

@[expose] public noncomputable def b : M24 :=
  ⟨bPerm, by exact b_word.symm ▸ (word bWord).property⟩

private def tWord : List (Fin 4) := [3, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0, 3, 0, 3, 3, 1, 3, 1, 2, 1, 3, 1, 2, 0, 2, 0, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 3, 0, 3, 0, 2, 0, 2, 0, 3, 0, 2, 0, 2, 0, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 0, 2, 0, 3, 0, 2, 0, 3, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 3, 0, 3, 0, 2, 0, 3, 0, 2, 0, 2, 0, 3, 0, 3, 0, 2, 0, 2, 0, 2, 1, 3, 1, 2, 1, 3, 1]

private theorem t_word : tPerm = (word tWord).val := by
  ext i
  fin_cases i <;> decide +kernel

@[expose] public noncomputable def t : M24 :=
  ⟨tPerm, by exact t_word.symm ▸ (word tWord).property⟩

public theorem a_cube : a ^ 3 = 1 := by
  apply Subtype.ext
  change aPerm ^ 3 = 1
  decide +kernel

public theorem b_cube : b ^ 3 = 1 := by
  apply Subtype.ext
  change bPerm ^ 3 = 1
  decide +kernel

public theorem commutator_a : Commute ⁅a, b⁆ a := by
  change ⁅a, b⁆ * a = a * ⁅a, b⁆
  apply Subtype.ext
  change ⁅aPerm, bPerm⁆ * aPerm = aPerm * ⁅aPerm, bPerm⁆
  decide +kernel

public theorem commutator_b : Commute ⁅a, b⁆ b := by
  change ⁅a, b⁆ * b = b * ⁅a, b⁆
  apply Subtype.ext
  change ⁅aPerm, bPerm⁆ * bPerm = bPerm * ⁅aPerm, bPerm⁆
  decide +kernel

public theorem commutator_ne_one : ⁅a, b⁆ ≠ 1 := by
  intro h
  have hp := congrArg (fun g : M24 => (g : Equiv.Perm (Fin 24)) 1) h
  have hn : (⁅aPerm, bPerm⁆ : Equiv.Perm (Fin 24)) 1 ≠ 1 := by decide +kernel
  exact hn hp

public theorem t_sq : t ^ 2 = 1 := by
  apply Subtype.ext
  change tPerm ^ 2 = 1
  decide +kernel

public theorem conjugate_a : t * a * t⁻¹ = a⁻¹ := by
  apply Subtype.ext
  change tPerm * aPerm * tPerm⁻¹ = aPerm⁻¹
  decide +kernel

public theorem conjugate_b : t * b * t⁻¹ = b⁻¹ := by
  apply Subtype.ext
  change tPerm * bPerm * tPerm⁻¹ = bPerm⁻¹
  decide +kernel

end Sporadic.Mathieu.M24ValueBoundParabolics.ThreeModel
