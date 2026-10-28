/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinIntegralGenerators.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.EisensteinGenerators
public import Theory.AtlasPort.OtherSporadic.Algebra.EisensteinSpan

/-!
# Eisenstein Integral Generators

The Eisenstein generators together with their omega multiples generate the integral lattice. The Eisenstein span criterion transfers to an integral span using the scalar basis 1, omega.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinIntegralGenerators.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for the source coordinate computations.
-/

@[expose] public section

namespace Atlas.Lattices
open Atlas.Algebra

theorem eisensteinLeechModule_integral_generators
    (S : Submodule ℤ EisensteinCoordinates)
    (hg : ∀ g ∈ eisensteinGeneratorSet, g ∈ S)
    (hω : ∀ g ∈ eisensteinGeneratorSet, eisensteinOmega • g ∈ S) :
    eisensteinLeechModule.restrictScalars ℤ ≤ S := by
  rw [eisensteinLeechModule_eq_span]
  exact eisensteinSpan_subset_intSubmodule _ S hg hω

/-- An explicit integral generating set, retaining both scalar basis elements. -/
def eisensteinIntegralGeneratorSet : Set EisensteinCoordinates :=
  eisensteinGeneratorSet ∪ ((fun z => eisensteinOmega • z) '' eisensteinGeneratorSet)

theorem eisensteinLeechModule_eq_integral_span :
    eisensteinLeechModule.restrictScalars ℤ =
      Submodule.span ℤ eisensteinIntegralGeneratorSet := by
  apply le_antisymm
  · apply eisensteinLeechModule_integral_generators
    · intro g hg
      exact Submodule.subset_span (Or.inl hg)
    · intro g hg
      exact Submodule.subset_span (Or.inr ⟨g, hg, rfl⟩)
  · apply Submodule.span_le.mpr
    intro z hz
    rcases hz with hz | ⟨g, hg, rfl⟩
    · exact eisensteinGeneratorSet_mem hz
    · exact eisensteinLeechModule.smul_mem _ (eisensteinGeneratorSet_mem hg)

end Atlas.Lattices
