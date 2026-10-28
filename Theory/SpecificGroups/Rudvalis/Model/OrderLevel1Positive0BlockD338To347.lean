module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockD308To317
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions: batches 338–347

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
private theorem batch338 : stepBatch 0 338 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch339 : stepBatch 0 339 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch340 : stepBatch 0 340 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch341 : stepBatch 0 341 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch342 : stepBatch 0 342 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch343 : stepBatch 0 343 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch344 : stepBatch 0 344 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch345 : stepBatch 0 345 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch346 : stepBatch 0 346 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch347 : stepBatch 0 347 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-0 transitions for batches 338 through 347. -/
public theorem segment338 (b : Fin 10) :
    stepBatch 0 ⟨338 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch338
  · exact batch339
  · exact batch340
  · exact batch341
  · exact batch342
  · exact batch343
  · exact batch344
  · exact batch345
  · exact batch346
  · exact batch347

end Rudvalis.OrderCertificate.OrderLevel1Positive0
