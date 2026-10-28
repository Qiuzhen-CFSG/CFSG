/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalFusionArithmetic.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Tactic

/-!
# Arithmetic for the five orthogonal orbits

Finite enumeration proves the total size and excludes a nonempty proper union
whose size is divisible by 23. Structural orbit identifications are separate.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/OrthogonalFusionArithmetic.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries.
-/

public section

namespace Atlas.Conway
open scoped BigOperators

/-- Arithmetic only; the five structural orbit identifications are separate obligations. -/
theorem orthogonal_five_sizes_total :
    (∑ i : Fin 5, ![2,924,42240,4928,45056] i) = (93150 : ℕ) := by decide

/-- No nonempty proper union of the five proposed orbit sizes is divisible by 23. -/
theorem orthogonal_five_sizes_fusion (S : Finset (Fin 5))
    (h : 23 ∣ ∑ i ∈ S, (![2,924,42240,4928,45056] i : ℕ)) :
    S = ∅ ∨ S = Finset.univ := by
  have hcheck : ∀ T : Finset (Fin 5),
      23 ∣ ∑ i ∈ T, (![2,924,42240,4928,45056] i : ℕ) → T = ∅ ∨ T = Finset.univ := by
    decide
  exact hcheck S h

end Atlas.Conway
