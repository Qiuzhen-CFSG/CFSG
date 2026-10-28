/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu11PointStabilizer
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimeDegree

/-!
# Mathieu11Simplicity

The degree-eleven point stabilizer of the dodecad action is simple. Its faithful doubly
transitive prime-degree action and proved order satisfy the prime-degree simplicity
criterion.

Source: `Atlas/Mathieu/Mathieu11Simplicity.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

theorem mathieu11_simple (D : Dodecad) (a : Mathieu12Points D) : IsSimpleGroup (Mathieu11PointModel D a) := by
  have := mathieu11_faithful D a
  have := mathieu11_four_transitive D a
  have : MulAction.IsMultiplyPretransitive (Mathieu11PointModel D a) (Mathieu11Points D a) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 4)
      (by rw [mathieu11_degree]; decide)
  have : MulAction.IsPretransitive (Mathieu11PointModel D a) (Mathieu11Points D a) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply Atlas.GroupTheory.prime_degree_simple (G := Mathieu11PointModel D a)
    (X := Mathieu11Points D a) 11 5 144 (by decide) (by decide) (by decide)
    (mathieu11_degree D a)
  rw [mathieu11_order]

end Atlas.Codes
