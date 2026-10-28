/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootFrameAction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointOrthogonality
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# IcosianRootFrameAction

The Hermitian action preserves orthogonality and acts on three-point root frames.
Equality of underlying point sets determines the resulting frame.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootFrameAction.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open scoped Pointwise
attribute [local instance] Classical.propDecidable

/-- The actual full Hermitian group acts on all unordered quaternionic root frames. -/
instance icosianHermitian_rootFrame_mulAction : MulAction icosianHermitianGroup IcosianRootFrame where
  smul g F := ⟨g • F.val,by
    constructor
    · rw [Finset.card_smul_finset,F.property.1]
    · intro p hp q hq hpq
      obtain ⟨a,ha,rfl⟩ := Finset.mem_smul_finset.mp hp
      obtain ⟨b,hb,rfl⟩ := Finset.mem_smul_finset.mp hq
      apply (icosianRootPointOrthogonal_smul_iff g a b).mpr
      exact F.property.2 ha hb (fun he => hpq (congrArg (g • ·) he))⟩
  one_smul F := Subtype.ext (one_smul _ _)
  mul_smul g h F := Subtype.ext (mul_smul _ _ _)

@[simp] theorem icosianRootFrame_smul_val (g : icosianHermitianGroup) (F : IcosianRootFrame) :
    (g • F).val=g • F.val := rfl

@[simp] theorem icosianRootFrame_smul_mem_iff (g : icosianHermitianGroup) (F : IcosianRootFrame)
    (p : IcosianRootPoint) : g • p∈(g • F).val ↔ p∈F.val :=
  Finset.smul_mem_smul_finset_iff g

/-- Point images determine the image of an actual unordered frame. -/
theorem icosianRootFrame_smul_eq_of_val (g : icosianHermitianGroup) (F G : IcosianRootFrame)
    (h : g • F.val=G.val) : g • F=G := Subtype.ext h

end Atlas.Conway
