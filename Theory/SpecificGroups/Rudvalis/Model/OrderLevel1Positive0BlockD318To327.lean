module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockD288To297
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions: batches 318–327

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
private theorem batch318 : stepBatch 0 318 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch319 : stepBatch 0 319 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch320 : stepBatch 0 320 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch321 : stepBatch 0 321 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch322 : stepBatch 0 322 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch323 : stepBatch 0 323 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch324 : stepBatch 0 324 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch325 : stepBatch 0 325 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch326 : stepBatch 0 326 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch327 : stepBatch 0 327 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-0 transitions for batches 318 through 327. -/
public theorem segment318 (b : Fin 10) :
    stepBatch 0 ⟨318 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch318
  · exact batch319
  · exact batch320
  · exact batch321
  · exact batch322
  · exact batch323
  · exact batch324
  · exact batch325
  · exact batch326
  · exact batch327

end Rudvalis.OrderCertificate.OrderLevel1Positive0
