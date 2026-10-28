/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/PrimitiveNormal.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# PrimitiveNormal

Nontrivial normal subgroups of faithful primitive permutation groups act transitively.
The proof applies the block property of normal-subgroup orbits.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/PrimitiveNormal.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

/-! Faithful primitive actions and point-stabilizer restriction. -/

namespace Atlas.GroupTheory

variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]

/-- A nontrivial normal subgroup in a faithful primitive action is transitive. -/
theorem normal_pretransitive [MulAction.IsPreprimitive G X]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : MulAction.IsPretransitive N X := by
  apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
  intro h
  apply hN
  apply le_antisymm _ bot_le
  intro n hn
  rw [Subgroup.mem_bot]
  apply eq_of_smul_eq_smul (α := X)
  intro x
  have hx : x ∈ MulAction.fixedPoints N X := by rw [h]; trivial
  exact (MulAction.mem_fixedPoints.mp hx ⟨n,hn⟩).trans (one_smul G x).symm

/-- Restriction to the complement of a fixed point retains faithfulness. -/
theorem stabilizer_complement_faithful (a : X) :
    FaithfulSMul (MulAction.stabilizer G a) (SubMulAction.ofStabilizer G a) where
  eq_of_smul_eq_smul {g h} he := by
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := X)
    intro x
    by_cases hx : x = a
    · subst x
      exact g.property.trans h.property.symm
    · exact congrArg Subtype.val (he ⟨x,hx⟩)


end Atlas.GroupTheory
