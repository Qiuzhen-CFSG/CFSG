/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu23Simplicity
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SimpleStabilizer

/-!
# Mathieu24Simplicity

The full Golay coordinate automorphism group is nonabelian simple. Its doubly transitive
action has a simple degree-twenty-three point stabilizer, and the two distinct prime
divisors of degree twenty-four discharge the simple-stabilizer criterion.

Source: `Atlas/Mathieu/Mathieu24Simplicity.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

/-! Nonabelian simplicity of the existing full coordinate automorphism group of Golay. -/

namespace Atlas.Codes

theorem mathieu24_simple : IsSimpleGroup Mathieu24CodeModel := by
  let a : Omega := ((0, 0), 0)
  have := mathieu24_five_transitive
  have : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 5)
      (by norm_num [Omega, HexIndex])
  have : IsSimpleGroup (MulAction.stabilizer Mathieu24CodeModel a) := mathieu23_simple a
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact Atlas.GroupTheory.simple_of_simple_stabilizer (G := Mathieu24CodeModel)
    (X := Omega) a 2 3 (by decide) (by norm_num [Omega, HexIndex])
    (by norm_num [Omega, HexIndex])

theorem mathieu24_nonabelian_simple : IsSimpleGroup Mathieu24CodeModel ∧
    ∃ g h : Mathieu24CodeModel, g * h ≠ h * g :=
  ⟨mathieu24_simple, mathieu24_noncommuting_pair⟩

end Atlas.Codes
