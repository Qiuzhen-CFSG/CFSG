/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/TransitiveFullStabilizer.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Subgroups containing a full stabilizer

A subgroup reaching each point of an ambient orbit and containing its full stabilizer equals the ambient group.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/TransitiveFullStabilizer.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.GroupTheory
open MulAction

/-- A subgroup reaching the whole ambient orbit and containing the full point
stabilizer is the whole group. No finiteness or faithful action is needed. -/
theorem subgroup_eq_top_of_full_stabilizer {G X : Type*} [Group G] [MulAction G X]
    (K : Subgroup G) (x : X) (hstab : stabilizer G x ≤ K)
    (horbit : ∀ g : G, ∃ k : K, k.val • x = g • x) : K = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨k, hk⟩ := horbit g
  have hm : k.val⁻¹*g ∈ stabilizer G x := by
    change (k.val⁻¹*g) • x = x
    rw [mul_smul, ← hk, inv_smul_smul]
  have h := K.mul_mem k.property (hstab hm)
  simpa only [mul_inv_cancel_left] using h

end Atlas.GroupTheory
