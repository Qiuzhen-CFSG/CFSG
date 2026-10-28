module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockD278To287
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions: batches 308–317

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
private theorem batch308 : stepBatch 0 308 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch309 : stepBatch 0 309 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch310 : stepBatch 0 310 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch311 : stepBatch 0 311 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch312 : stepBatch 0 312 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch313 : stepBatch 0 313 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch314 : stepBatch 0 314 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch315 : stepBatch 0 315 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch316 : stepBatch 0 316 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch317 : stepBatch 0 317 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-0 transitions for batches 308 through 317. -/
public theorem segment308 (b : Fin 10) :
    stepBatch 0 ⟨308 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch308
  · exact batch309
  · exact batch310
  · exact batch311
  · exact batch312
  · exact batch313
  · exact batch314
  · exact batch315
  · exact batch316
  · exact batch317

end Rudvalis.OrderCertificate.OrderLevel1Positive0
