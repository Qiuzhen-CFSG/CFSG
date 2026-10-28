module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 1: batches 160–175

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
private theorem batch160 : stepBatch 1 160 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch161 : stepBatch 1 161 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch162 : stepBatch 1 162 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch163 : stepBatch 1 163 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch164 : stepBatch 1 164 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch165 : stepBatch 1 165 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch166 : stepBatch 1 166 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch167 : stepBatch 1 167 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch168 : stepBatch 1 168 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch169 : stepBatch 1 169 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch170 : stepBatch 1 170 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch171 : stepBatch 1 171 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch172 : stepBatch 1 172 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch173 : stepBatch 1 173 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch174 : stepBatch 1 174 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch175 : stepBatch 1 175 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The transitions for representatives 640–703. -/
public theorem block10 (b : Fin 16) : stepBatch 1 ⟨160 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch160
  · exact batch161
  · exact batch162
  · exact batch163
  · exact batch164
  · exact batch165
  · exact batch166
  · exact batch167
  · exact batch168
  · exact batch169
  · exact batch170
  · exact batch171
  · exact batch172
  · exact batch173
  · exact batch174
  · exact batch175

end Rudvalis.OrderCertificate.OrderLevel2Positive1
