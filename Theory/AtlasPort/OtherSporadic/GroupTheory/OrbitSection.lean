/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/OrbitSection.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Equivariant maps from stabilizer containment

Choose orbit representatives and use stabilizer containment to prove equivariance.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/OrbitSection.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies are exposed where the downstream stabilizer constructions use reduction.
-/

@[expose] public section

noncomputable section
namespace Atlas.GroupTheory

/-- A stabilizer containment induces an equivariant map from a transitive set. -/
theorem exists_equivariant_map_of_stabilizer {G X Y : Type*} [Group G]
    [MulAction G X] [MulAction G Y] [MulAction.IsPretransitive G X]
    (x : X) (y : Y) (h : ∀ g : G, g • x = x → g • y = y) :
    ∃ f : X → Y, f x = y ∧ (∀ (g : G) (z : X), f (g • z) = g • f z) ∧
      ∀ z, ∃ g : G, g • x = z ∧ f z = g • y := by
  choose s hs using (fun z : X => MulAction.exists_smul_eq G x z)
  let f : X → Y := fun z => s z • y
  have he (g : G) (z : X) : f (g • z) = g • f z := by
    have ht : ((s (g • z))⁻¹ * g * s z) • x = x := by
      simp only [mul_smul,hs]
      exact inv_smul_eq_iff.mpr (hs (g • z)).symm
    have hh := h _ ht
    simp only [mul_smul] at hh
    exact (inv_smul_eq_iff.mp hh).symm
  refine ⟨f,h (s x) (hs x),he,?_⟩
  intro z
  exact ⟨s z,hs z,rfl⟩

end Atlas.GroupTheory
