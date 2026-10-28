/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/EisensteinCancellation.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.EisensteinRational

/-!
# Cancellation in the Eisenstein integers

The embedding in the rational Eisenstein field transfers multiplicative cancellation to integral scalars.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/EisensteinCancellation.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.Algebra

theorem eisenstein_mul_left_cancel {a b c : Eisenstein} (ha : a≠0) (h : a*b=a*c) : b=c := by
  apply eisensteinToRational_injective
  have haK : eisensteinToRational a≠0 := by
    intro hz
    apply ha
    apply eisensteinToRational_injective
    simpa using hz
  apply mul_left_cancel₀ haK
  simpa only [← map_mul] using congrArg eisensteinToRational h

end Atlas.Algebra
