/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Fischer/ResiduePrimitivityArithmetic.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.RankThreePrimitivity
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Fischer rank-three arithmetic

The three concrete degrees and their subdegrees satisfy the singleton and sum
identities and exclude proper nonsingleton block sizes by divisibility.
The proofs reduce the three cases to finite arithmetic.

Source: Gerald Höhn, ATLAS, `Atlas/Fischer/ResiduePrimitivityArithmetic.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream calculations.
-/

@[expose] public section

namespace Atlas.Fischer

/-- The three numerical targets, separated from the actual orbit proofs. -/
def fischerRankThreeDegree : Fin 3 → ℕ := ![306936,31671,3510]

def fischerRankThreeSubdegree : Fin 3 → Fin 3 → ℕ :=
  ![![1,31671,275264],![1,3510,28160],![1,693,2816]]

theorem fischerRankThree_singleton (s : Fin 3) : fischerRankThreeSubdegree s 0=1 := by
  fin_cases s <;> rfl

theorem fischerRankThree_degree_sum (s : Fin 3) :
    fischerRankThreeDegree s=1+fischerRankThreeSubdegree s 1+fischerRankThreeSubdegree s 2 := by
  fin_cases s <;> rfl

theorem fischerRankThree_first_nondivisibility (s : Fin 3) :
    ¬(1+fischerRankThreeSubdegree s 1) ∣ fischerRankThreeDegree s := by
  fin_cases s <;> decide

theorem fischerRankThree_second_nondivisibility (s : Fin 3) :
    ¬(1+fischerRankThreeSubdegree s 2) ∣ fischerRankThreeDegree s := by
  fin_cases s <;> decide

end Atlas.Fischer
