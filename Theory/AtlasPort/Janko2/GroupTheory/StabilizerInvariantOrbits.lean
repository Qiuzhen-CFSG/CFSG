/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/StabilizerInvariantOrbits.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# StabilizerInvariantOrbits

An invariant separates stabilizer orbits when its fibers are transitive.
The proofs compare orbit membership with equality of invariant values.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/StabilizerInvariantOrbits.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


namespace Atlas

/-- Orbits of a point stabilizer may be obtained by interchanging the two
coordinates of an invariant relation. Only the stabilizer of one reference
point needs to be analyzed. -/
theorem stabilizer_transitive_of_reference_invariant
    {G X Y Z : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (f : X → Y → Z) (hf : ∀ (g : G) (x : X) (y : Y), f (g • x) (g • y)=f x y)
    (x₀ : X) (y₀ : Y)
    (href : ∀ y z, f x₀ y=f x₀ z →
      ∃ g : G, g • x₀=x₀ ∧ g • y=z)
    (x₁ x₂ : X) (h₁ : x₁∈MulAction.orbit G x₀)
    (h₂ : x₂∈MulAction.orbit G x₀) (he : f x₁ y₀=f x₂ y₀) :
    ∃ g : G, g • y₀=y₀ ∧ g • x₁=x₂ := by
  obtain ⟨a,rfl⟩ := h₁
  obtain ⟨b,rfl⟩ := h₂
  have ht : f x₀ (a⁻¹ • y₀)=f x₀ (b⁻¹ • y₀) := by
    have ha := hf a x₀ (a⁻¹ • y₀)
    have hb := hf b x₀ (b⁻¹ • y₀)
    simp only [smul_inv_smul] at ha hb
    exact ha.symm.trans (he.trans hb)
  obtain ⟨c,hc,hcy⟩ := href _ _ ht
  refine ⟨b*c*a⁻¹,?_,?_⟩
  · simp only [mul_smul]
    rw [hcy,smul_inv_smul]
  · simp only [mul_smul,inv_smul_smul,hc]

end Atlas
