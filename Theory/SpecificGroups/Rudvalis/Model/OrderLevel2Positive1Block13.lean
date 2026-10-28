module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 1: batches 208–223

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
private theorem batch208 : stepBatch 1 208 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch209 : stepBatch 1 209 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch210 : stepBatch 1 210 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch211 : stepBatch 1 211 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch212 : stepBatch 1 212 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch213 : stepBatch 1 213 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch214 : stepBatch 1 214 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch215 : stepBatch 1 215 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch216 : stepBatch 1 216 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch217 : stepBatch 1 217 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch218 : stepBatch 1 218 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch219 : stepBatch 1 219 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch220 : stepBatch 1 220 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch221 : stepBatch 1 221 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch222 : stepBatch 1 222 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch223 : stepBatch 1 223 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The transitions for representatives 832–895. -/
public theorem block13 (b : Fin 16) : stepBatch 1 ⟨208 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch208
  · exact batch209
  · exact batch210
  · exact batch211
  · exact batch212
  · exact batch213
  · exact batch214
  · exact batch215
  · exact batch216
  · exact batch217
  · exact batch218
  · exact batch219
  · exact batch220
  · exact batch221
  · exact batch222
  · exact batch223

end Rudvalis.OrderCertificate.OrderLevel2Positive1
