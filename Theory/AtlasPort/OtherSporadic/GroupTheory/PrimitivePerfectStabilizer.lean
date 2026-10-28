/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/PrimitivePerfectStabilizer.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Theory.AtlasPort.OtherSporadic.GroupTheory.TransitiveFullStabilizer
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfectness from a primitive stabilizer

Normal transitivity and a full point stabilizer force a normal subgroup to be the whole group, yielding perfectness from a perfect stabilizer.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/PrimitivePerfectStabilizer.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.GroupTheory
open MulAction

/-- In a faithful primitive action, a nontrivial normal subgroup containing a
full point stabilizer is the whole group. -/
theorem normal_eq_top_of_full_stabilizer {G X : Type*} [Group G] [MulAction G X]
    [FaithfulSMul G X] [IsPreprimitive G X] (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) (x : X) (hx : stabilizer G x ≤ N) : N = ⊤ := by
  let := normal_pretransitive (X := X) N hN
  apply subgroup_eq_top_of_full_stabilizer N x hx
  intro g
  exact exists_smul_eq N x (g • x)

/-- A nontrivial perfect full point stabilizer forces a faithful primitive group
to be perfect. This uses its actual commutator subgroup, not an order argument. -/
theorem perfect_of_perfect_stabilizer {G X : Type*} [Group G] [MulAction G X]
    [FaithfulSMul G X] [IsPreprimitive G X] (x : X)
    [Group.IsPerfect (stabilizer G x)] (hx : stabilizer G x ≠ ⊥) : Group.IsPerfect G := by
  have hs : stabilizer G x ≤ commutator G := by
    rw [← Subgroup.commutator_eq_self (H := stabilizer G x)]
    exact Subgroup.commutator_mono le_top le_top
  constructor
  exact normal_eq_top_of_full_stabilizer (commutator G)
    (fun h => hx (le_antisymm (h ▸ hs) bot_le)) x hs

end Atlas.GroupTheory
