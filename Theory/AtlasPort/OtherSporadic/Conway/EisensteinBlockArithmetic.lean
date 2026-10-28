/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/EisensteinBlockArithmetic.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-!
# Arithmetic of the Suzuki subdegrees

Kernel-checked enumeration of the 4096 subsets gives a block-size obstruction for the prescribed twelve nontrivial subdegrees. The geometric identification of these subdegrees is a separate theorem.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/EisensteinBlockArithmetic.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.Conway
open scoped BigOperators

/-- The twelve proposed nontrivial subdegrees, with repeated values retained.
This definition alone makes no orbit assertion. -/
def eisensteinNontrivialSubdegree : Fin 12 → ℕ :=
  ![165, 891, 2673, 2673, 2916, 16038, 16038, 17820, 40095, 40095, 40095, 53460]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Arithmetic obstruction for the prescribed subdegrees. Application to blocks
requires a separate proof that these are the actual stabilizer orbits. -/
theorem eisenstein_subdegree_block_arithmetic (S : Finset (Fin 12))
    (hd : (1 + ∑ i ∈ S, eisensteinNontrivialSubdegree i) ∣ 232960) :
    S = ∅ ∨ S = Finset.univ := by
  revert hd S
  decide +kernel

end Atlas.Conway
