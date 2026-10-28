module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/FaithfulAction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.ExactStabilizer
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Faithfulness of the actual generated matrix group on its projective point set. -/
theorem pointAction_faithful (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    letI := pointAction m hcard
    FaithfulSMul (Model F m) (pointSet (F := F) m) := by
  letI := pointAction m hcard
  apply faithfulSMul_iff.mpr
  intro g hg
  have hf : ∀ p ∈ pointSet m, pointRight g.val⁻¹ p = p := by
    intro p hp
    exact congrArg Subtype.val (hg ⟨p,hp⟩)
  have hb : g.val⁻¹ ∈ borel m hcard :=
    (fixes_infinity_iff_mem_borel m hcard _ ((generated F m).inv_mem g.property)).mp
      (hf infinityPoint ⟨none,rfl⟩)
  have he := congrArg Subtype.val (borel_action_faithful m hcard ⟨g.val⁻¹,hb⟩ hf)
  apply Subtype.ext
  change g.val = 1
  exact inv_eq_one.mp he

end Atlas.ReeG2
