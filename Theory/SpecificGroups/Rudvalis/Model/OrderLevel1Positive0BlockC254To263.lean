module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions: batches 254–263

This checkpoint certifies the five representatives in each indicated batch for
positive generator 0. The checker proves free word cancellation or checks the
permutations at all 4060 points in Lean's kernel.

Source: the ATLAS-derived witnesses documented in `OrderLevel1Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch254 : stepBatch 0 254 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch255 : stepBatch 0 255 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch256 : stepBatch 0 256 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch257 : stepBatch 0 257 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch258 : stepBatch 0 258 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch259 : stepBatch 0 259 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch260 : stepBatch 0 260 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch261 : stepBatch 0 261 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch262 : stepBatch 0 262 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch263 : stepBatch 0 263 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-0 transitions for batches 254 through 263. -/
public theorem segment254 (b : Fin 10) :
    stepBatch 0 ⟨254 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch254
  · exact batch255
  · exact batch256
  · exact batch257
  · exact batch258
  · exact batch259
  · exact batch260
  · exact batch261
  · exact batch262
  · exact batch263

end Rudvalis.OrderCertificate.OrderLevel1Positive0
