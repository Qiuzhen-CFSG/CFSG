module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/GroupTheory/ActionInvolutionSign.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
The sign of an involution acting on a finite set is determined by the
number of moved points, since each nontrivial orbit is a transposition.
-/

@[expose] public section

namespace Atlas.GroupTheory

/-- The sign of an involution is determined by its fixed-point count. -/
theorem action_sign_involution {G X : Type*} [Group G] [MulAction G X]
    [Fintype X] [DecidableEq X] (g : G) (hg : g^2=1) :
    Equiv.Perm.sign (MulAction.toPermHom G X g) =
      (-1)^((Nat.card X-Nat.card {x:X // g • x=x})/2) := by
  have hp : (MulAction.toPermHom G X g)^2=1 := by rw [← map_pow,hg,map_one]
  rw [Equiv.Perm.sign_of_pow_two_eq_one hp]
  congr 2
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  rfl

end Atlas.GroupTheory
