module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 1: batches 192–207

These four-representative batches use free cancellation where possible and
otherwise check the permutation identity on all 4060 points in Lean's kernel.
The ranges are separate compilation units to bound certificate checking cost.

Source: the ATLAS degree-4060 witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive1
open Level2Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch192 : stepBatch 1 192 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch193 : stepBatch 1 193 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch194 : stepBatch 1 194 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch195 : stepBatch 1 195 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch196 : stepBatch 1 196 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch197 : stepBatch 1 197 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch198 : stepBatch 1 198 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch199 : stepBatch 1 199 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch200 : stepBatch 1 200 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch201 : stepBatch 1 201 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch202 : stepBatch 1 202 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch203 : stepBatch 1 203 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch204 : stepBatch 1 204 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch205 : stepBatch 1 205 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch206 : stepBatch 1 206 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch207 : stepBatch 1 207 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The transitions for representatives 768–831. -/
public theorem block12 (b : Fin 16) : stepBatch 1 ⟨192 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch192
  · exact batch193
  · exact batch194
  · exact batch195
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

end Rudvalis.OrderCertificate.OrderLevel2Positive1
