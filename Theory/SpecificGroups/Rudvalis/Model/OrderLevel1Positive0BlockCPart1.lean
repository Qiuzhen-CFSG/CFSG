module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockCPart0
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions, batches 196–207

Each batch verifies five orbit representatives by free cancellation or kernel
checking on all 4060 points. These compilation checkpoints use the ATLAS-derived
witnesses documented in `OrderLevel1Data` and `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0.BlockC
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch196 : stepBatch 0 196 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch197 : stepBatch 0 197 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch198 : stepBatch 0 198 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch199 : stepBatch 0 199 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch200 : stepBatch 0 200 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch201 : stepBatch 0 201 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch202 : stepBatch 0 202 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch203 : stepBatch 0 203 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch204 : stepBatch 0 204 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch205 : stepBatch 0 205 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch206 : stepBatch 0 206 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch207 : stepBatch 0 207 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- Positive-generator-0 transitions for batches 196 through 207. -/
public theorem part1 (b : Fin 12) : stepBatch 0 ⟨196 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch196
  · exact batch197
  · exact batch198
  · exact batch199
  · exact batch200
  · exact batch201
  · exact batch202
  · exact batch203
  · exact batch204
  · exact batch205
  · exact batch206
  · exact batch207

end Rudvalis.OrderCertificate.OrderLevel1Positive0.BlockC
