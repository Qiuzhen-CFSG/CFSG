/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu21Simplicity

/-!
# Simplicity of the two-point stabilizer

The stabilizer of two distinct Golay coordinates is simple. Its faithful
three-transitive action has degree 22; the simple M₂₁ point stabilizer and the
prime factors 2 and 11 discharge the simple-stabilizer criterion.

Source: `Atlas/Mathieu/Mathieu22Simplicity.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

theorem mathieu22_simple (a : Omega) (b : Mathieu23Points a) :
    IsSimpleGroup (Mathieu22PointModel a b) := by
  have := mathieu22_faithful a b
  have := mathieu22_three_transitive a b
  have : MulAction.IsMultiplyPretransitive (Mathieu22PointModel a b) (Mathieu22Points a b) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 3) (by rw [mathieu22_degree]; decide)
  obtain ⟨c⟩ := (Nat.card_pos_iff.mp (show 0 < Nat.card (Mathieu22Points a b) by
    rw [mathieu22_degree]; decide)).1
  have := mathieu21_simple a b c
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact Atlas.GroupTheory.simple_of_simple_stabilizer c 2 11 (by decide)
    (by rw [mathieu22_degree]; decide) (by rw [mathieu22_degree]; decide)

end Atlas.Codes
