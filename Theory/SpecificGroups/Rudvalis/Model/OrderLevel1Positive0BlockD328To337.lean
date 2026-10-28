module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockD298To307
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions: batches 328–337

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
private theorem batch328 : stepBatch 0 328 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch329 : stepBatch 0 329 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch330 : stepBatch 0 330 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch331 : stepBatch 0 331 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch332 : stepBatch 0 332 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch333 : stepBatch 0 333 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch334 : stepBatch 0 334 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch335 : stepBatch 0 335 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch336 : stepBatch 0 336 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch337 : stepBatch 0 337 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-0 transitions for batches 328 through 337. -/
public theorem segment328 (b : Fin 10) :
    stepBatch 0 ⟨328 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch328
  · exact batch329
  · exact batch330
  · exact batch331
  · exact batch332
  · exact batch333
  · exact batch334
  · exact batch335
  · exact batch336
  · exact batch337

end Rudvalis.OrderCertificate.OrderLevel1Positive0
