module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Trio

/-!
# A concrete elementary-nine candidate outside the trio geometry

These two permutations fix point 1 and commute. Their subgroup has a
nine-point orbit, which will obstruct preservation of any octad trio.
Membership in the actual Witt-design automorphism group is certified by words
in the existing ATLAS standard generators. GAP supplied only the word data;
Lean checks each word at every point. Words are evaluated in reverse order
because GAP composes its permutations on the right.

Source context: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511;
Aschbacher, *Sporadic Groups*, Chapter 7, §20. These certificates diagnose an
overstrong proposed universal placement in the trio stabilizer; they do not
assert the existence of a permuting Sylow pair.
-/

@[expose] public section

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TrioObstruction

set_option maxRecDepth 100000

def xPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [4,5,8] * List.formPerm [6,13,19] *
  List.formPerm [7,17,14] * List.formPerm [9,11,12] *
  List.formPerm [10,24,22] * List.formPerm [15,18,20]

def yPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [2,3,16] * List.formPerm [4,8,5] *
  List.formPerm [6,7,15] * List.formPerm [10,24,22] *
  List.formPerm [13,17,18] * List.formPerm [14,20,19]

private noncomputable def letter : Fin 3 → M24
  | 0 => ⟨m24GeneratorA, m24GeneratorA_mem⟩
  | 1 => ⟨m24GeneratorB, m24GeneratorB_mem⟩
  | 2 => ⟨m24GeneratorB, m24GeneratorB_mem⟩⁻¹

private noncomputable def word : List (Fin 3) → M24
  | [] => 1
  | i :: w => word w * letter i

private def xWord : List (Fin 3) := [2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0]

private theorem x_word : xPerm = (word xWord).val := by
  ext i
  fin_cases i <;> decide +kernel

private theorem x_mem : xPerm ∈ M24 :=
  x_word.symm ▸ (word xWord).property

private def yWord : List (Fin 3) := [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1]

private theorem y_word : yPerm = (word yWord).val := by
  ext i
  fin_cases i <;> decide +kernel

private theorem y_mem : yPerm ∈ M24 :=
  y_word.symm ▸ (word yWord).property

/-- The first checked order-three element in the fixed Witt-design carrier. -/
noncomputable def x : M24 := ⟨xPerm, by exact x_mem⟩

/-- The second checked order-three element in the same carrier. -/
noncomputable def y : M24 := ⟨yPerm, by exact y_mem⟩

@[simp] theorem x_coe : (x : Equiv.Perm (Fin 24)) = xPerm := rfl
@[simp] theorem y_coe : (y : Equiv.Perm (Fin 24)) = yPerm := rfl

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TrioObstruction

end
