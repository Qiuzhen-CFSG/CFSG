module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockD318To327
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions: batches 348–350

This checkpoint certifies the five representatives in each indicated batch for
positive generator 0. The checker proves free word cancellation or checks the
permutations at all 4060 points in Lean's kernel. Checkpoints are imported in three
chains to bound concurrent memory-intensive checks during a combined Lake build.

Source: the ATLAS-derived witnesses documented in `OrderLevel1Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch348 : stepBatch 0 348 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch349 : stepBatch 0 349 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch350 : stepBatch 0 350 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-0 transitions for batches 348 through 350. -/
public theorem segment348 (b : Fin 3) :
    stepBatch 0 ⟨348 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch348
  · exact batch349
  · exact batch350

end Rudvalis.OrderCertificate.OrderLevel1Positive0
