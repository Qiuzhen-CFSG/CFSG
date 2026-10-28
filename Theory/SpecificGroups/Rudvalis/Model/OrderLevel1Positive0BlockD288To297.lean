module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions: batches 288–297

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
private theorem batch288 : stepBatch 0 288 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch289 : stepBatch 0 289 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch290 : stepBatch 0 290 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch291 : stepBatch 0 291 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch292 : stepBatch 0 292 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch293 : stepBatch 0 293 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch294 : stepBatch 0 294 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch295 : stepBatch 0 295 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch296 : stepBatch 0 296 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch297 : stepBatch 0 297 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-0 transitions for batches 288 through 297. -/
public theorem segment288 (b : Fin 10) :
    stepBatch 0 ⟨288 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch288
  · exact batch289
  · exact batch290
  · exact batch291
  · exact batch292
  · exact batch293
  · exact batch294
  · exact batch295
  · exact batch296
  · exact batch297

end Rudvalis.OrderCertificate.OrderLevel1Positive0
