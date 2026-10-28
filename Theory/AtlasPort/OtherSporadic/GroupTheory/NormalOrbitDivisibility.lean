/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/NormalOrbitDivisibility.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Divisibility of normal-subgroup orbits

Restricting to a full orbit turns a normal-subgroup orbit into a block, giving divisibility of orbit cardinalities.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/NormalOrbitDivisibility.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

noncomputable section
namespace Atlas.GroupTheory

/-- A normal-subgroup orbit has cardinality dividing the containing full orbit.
The argument restricts to the transitive full orbit and uses the block theorem. -/
theorem normal_orbit_card_dvd {H X : Type*} [Group H] [MulAction H X]
    (P : Subgroup H) [P.Normal] (x : X) :
    Nat.card (MulAction.orbit P x) ∣ Nat.card (MulAction.orbit H x) := by
  let y : MulAction.orbit H x := ⟨x,MulAction.mem_orbit_self x⟩
  let e : MulAction.orbit P y ≃ MulAction.orbit P x :=
    { toFun := fun z => ⟨z.val.val,MulAction.mem_subgroup_orbit_iff.mp z.property⟩
      invFun := fun z => ⟨⟨z.val,MulAction.orbit_subgroup_subset P x z.property⟩,
        MulAction.mem_subgroup_orbit_iff.mpr z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := (MulAction.IsBlock.orbit_of_normal (G := H) (N := P) y).ncard_dvd_card
    ⟨y,MulAction.mem_orbit_self y⟩
  change Nat.card (MulAction.orbit P y) ∣ Nat.card (MulAction.orbit H x) at h
  rwa [Nat.card_congr e] at h

end Atlas.GroupTheory
