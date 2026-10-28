/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu23PointStabilizer
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimeDegree

/-!
# Mathieu23Simplicity

The concrete degree-twenty-three coordinate stabilizer is simple. Its faithful prime-
degree action and computed order satisfy the prime-degree criterion; the nonprime order
then excludes commutativity.

Source: `Atlas/Mathieu/Mathieu23Simplicity.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

/-! Nonabelian simplicity of the actual 23-point stabilizer of the Golay code group. -/

namespace Atlas.Codes

theorem mathieu23_simple (a : Omega) : IsSimpleGroup (Mathieu23PointModel a) := by
  have := mathieu23_faithful a
  have := mathieu23_four_transitive a
  have : MulAction.IsMultiplyPretransitive (Mathieu23PointModel a) (Mathieu23Points a) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 4)
      (by rw [mathieu23_degree]; decide)
  have : MulAction.IsPretransitive (Mathieu23PointModel a) (Mathieu23Points a) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have : Fact (Nat.Prime 23) := ⟨by decide⟩
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply Atlas.GroupTheory.prime_degree_simple (G := Mathieu23PointModel a)
    (X := Mathieu23Points a) 23 11 40320 (by decide) (by decide) (by decide)
    (mathieu23_degree a)
  rw [mathieu23_order]

theorem mathieu23_noncommuting_pair (a : Omega) :
    ∃ g h : Mathieu23PointModel a, g * h ≠ h * g := by
  classical
  by_contra h
  push Not at h
  have : IsMulCommutative (Mathieu23PointModel a) := ⟨⟨h⟩⟩
  have := mathieu23_simple a
  have hp := (Group.is_simple_iff_prime_card (α := Mathieu23PointModel a)).mp
    (mathieu23_simple a)
  rw [mathieu23_order] at hp
  norm_num at hp

end Atlas.Codes
