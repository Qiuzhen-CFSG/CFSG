module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 1: batches 80–95

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
private theorem batch80 : stepBatch 1 80 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch81 : stepBatch 1 81 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch82 : stepBatch 1 82 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch83 : stepBatch 1 83 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch84 : stepBatch 1 84 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch85 : stepBatch 1 85 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch86 : stepBatch 1 86 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch87 : stepBatch 1 87 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch88 : stepBatch 1 88 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch89 : stepBatch 1 89 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch90 : stepBatch 1 90 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch91 : stepBatch 1 91 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch92 : stepBatch 1 92 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch93 : stepBatch 1 93 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch94 : stepBatch 1 94 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch95 : stepBatch 1 95 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The transitions for representatives 320–383. -/
public theorem block5 (b : Fin 16) : stepBatch 1 ⟨80 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch80
  · exact batch81
  · exact batch82
  · exact batch83
  · exact batch84
  · exact batch85
  · exact batch86
  · exact batch87
  · exact batch88
  · exact batch89
  · exact batch90
  · exact batch91
  · exact batch92
  · exact batch93
  · exact batch94
  · exact batch95

end Rudvalis.OrderCertificate.OrderLevel2Positive1
