module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions: batches 268–277

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
private theorem batch268 : stepBatch 0 268 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch269 : stepBatch 0 269 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch270 : stepBatch 0 270 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch271 : stepBatch 0 271 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch272 : stepBatch 0 272 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch273 : stepBatch 0 273 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch274 : stepBatch 0 274 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch275 : stepBatch 0 275 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch276 : stepBatch 0 276 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch277 : stepBatch 0 277 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-0 transitions for batches 268 through 277. -/
public theorem segment268 (b : Fin 10) :
    stepBatch 0 ⟨268 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch268
  · exact batch269
  · exact batch270
  · exact batch271
  · exact batch272
  · exact batch273
  · exact batch274
  · exact batch275
  · exact batch276
  · exact batch277

end Rudvalis.OrderCertificate.OrderLevel1Positive0
