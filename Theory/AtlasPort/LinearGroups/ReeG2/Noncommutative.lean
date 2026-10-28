module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/Noncommutative.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.RootGroup
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

theorem root_noncommutative (m : ℕ) (hcard : Nat.card F = 3^(2*m+1)) :
    rootElement (F := F) m 1 0 0 * rootElement m 0 1 0 ≠
      rootElement m 0 1 0 * rootElement m 1 0 0 := by
  intro h
  rw [rootElement_mul m hcard, rootElement_mul m hcard] at h
  simp at h
  have hp : ((1 : F), (1 : F), (0 : F)) = (1,1,-1) := rootMatrix_injective m (congrArg Units.val h)
  have hc := congrArg (fun p : F × F × F => p.2.2) hp
  simpa using hc

theorem model_noncommutative (m : ℕ) (hcard : Nat.card F = 3^(2*m+1)) :
    ∃ g h : Model F m, g * h ≠ h * g := by
  let x : Model F m := ⟨rootElement m 1 0 0,
    rootSubgroup_le_generated m hcard ⟨(1,0,0),rfl⟩⟩
  let y : Model F m := ⟨rootElement m 0 1 0,
    rootSubgroup_le_generated m hcard ⟨(0,1,0),rfl⟩⟩
  refine ⟨x,y,?_⟩
  intro h
  exact root_noncommutative m hcard (congrArg Subtype.val h)
end Atlas.ReeG2
