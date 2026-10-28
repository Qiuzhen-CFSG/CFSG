/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/CommutingFrameExtension.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.ThreeTranspositionFrames
public import Mathlib.Order.Preorder.Finite

/-!
# Extension of commuting sets to frames

A maximal element among commuting subsets of a finite distinguished set
extends any prescribed commuting subset to a frame.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/CommutingFrameExtension.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream calculations.
-/

@[expose] public section

noncomputable section
namespace Atlas.GroupTheory

/-- Every commuting subset of a distinguished set in a finite group extends
to a maximal commuting frame. -/
theorem exists_commutingFrame_containing {G : Type*} [Group G] [Finite G]
    (D S : Set G) (hS : S ⊆ D) (hc : ∀ x ∈ S, ∀ y ∈ S, Commute x y) :
    ∃ F : Set G, IsCommutingFrame D F ∧ S ⊆ F := by
  let C : Set (Set G) := {F | F ⊆ D ∧ (∀ x ∈ F, ∀ y ∈ F, Commute x y) ∧ S ⊆ F}
  obtain ⟨F,hF,hmax⟩ := (Set.toFinite C).exists_maximal (show C.Nonempty from
    ⟨S,hS,hc,Set.Subset.refl S⟩)
  refine ⟨F,⟨hF.1,hF.2.1,?_⟩,hF.2.2⟩
  intro E hE hcE hFE
  apply Set.Subset.antisymm _ hFE
  exact hmax ⟨hE,hcE,hF.2.2.trans hFE⟩ hFE

end Atlas.GroupTheory
