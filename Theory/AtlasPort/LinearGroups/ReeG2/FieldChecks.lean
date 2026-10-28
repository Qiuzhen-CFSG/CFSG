module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/FieldChecks.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.FieldTheory.ReeTitsAutomorphism
public import Mathlib.FieldTheory.Finite.GaloisField

@[expose] public section

/-! Canonical-field specializations of the uniform field-twist identities. -/
noncomputable section
namespace Atlas.ReeG2

theorem parameters27 : Parameters (GaloisField 3 3) 1 := by
  constructor
  · omega
  · simpa using GaloisField.card 3 3 (by omega)

theorem parameters243 : Parameters (GaloisField 3 5) 2 := by
  constructor
  · omega
  · simpa using GaloisField.card 3 5 (by omega)

theorem sigma_square27 (x : GaloisField 3 3) : sigma _ 1 (sigma _ 1 x) = x ^ 3 :=
  sigma_square parameters27.cardinality x

theorem sigma_square243 (x : GaloisField 3 5) : sigma _ 2 (sigma _ 2 x) = x ^ 3 :=
  sigma_square parameters243.cardinality x
end Atlas.ReeG2
