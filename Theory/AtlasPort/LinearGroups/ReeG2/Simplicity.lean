module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/Simplicity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.Perfect
public import Theory.AtlasPort.LinearGroups.ReeG2.FaithfulAction
public import Theory.AtlasPort.LinearGroups.ReeG2.Order
public import Theory.AtlasPort.LinearGroups.ReeG2.BorelSolvable
public import Theory.AtlasPort.LinearGroups.ReeG2.Noncommutative
public import Theory.AtlasPort.GroupTheory.SolvableStabilizerSimplicity
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Simplicity of the actual seven-dimensional Ree matrix group for every q≥27. -/
theorem simple (m : ℕ) (hp : Parameters F m) : IsSimpleGroup (Model F m) := by
  letI := pointAction m hp.cardinality
  letI : Nontrivial (Model F m) := by
    obtain ⟨g,h,hne⟩ := model_noncommutative m hp.cardinality
    exact ⟨⟨g*h,h*g,hne⟩⟩
  letI := perfect m hp
  letI := pointAction_preprimitive m hp.cardinality
  letI := pointAction_faithful m hp.cardinality
  letI := borel_solvable m hp.cardinality
  letI : Group.IsSolvable (MulAction.stabilizer (Model F m) (infinity (F := F) m)) := by
    rw [infinityStabilizer_eq_borel m hp.cardinality]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (borel_le_generated m hp.cardinality)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (borel_le_generated m hp.cardinality)).injective
  exact Atlas.GroupTheory.simple_of_perfect_quasiprimitive_solvable_stabilizer
    (infinity (F := F) m)

end Atlas.ReeG2
