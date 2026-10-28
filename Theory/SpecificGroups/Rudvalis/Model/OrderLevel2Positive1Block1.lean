module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 1: batches 16–31

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
private theorem batch16 : stepBatch 1 16 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch17 : stepBatch 1 17 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch18 : stepBatch 1 18 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch19 : stepBatch 1 19 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch20 : stepBatch 1 20 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch21 : stepBatch 1 21 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch22 : stepBatch 1 22 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch23 : stepBatch 1 23 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch24 : stepBatch 1 24 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch25 : stepBatch 1 25 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch26 : stepBatch 1 26 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch27 : stepBatch 1 27 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch28 : stepBatch 1 28 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch29 : stepBatch 1 29 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch30 : stepBatch 1 30 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 1600000 in
private theorem batch31 : stepBatch 1 31 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The transitions for representatives 64–127. -/
public theorem block1 (b : Fin 16) : stepBatch 1 ⟨16 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch16
  · exact batch17
  · exact batch18
  · exact batch19
  · exact batch20
  · exact batch21
  · exact batch22
  · exact batch23
  · exact batch24
  · exact batch25
  · exact batch26
  · exact batch27
  · exact batch28
  · exact batch29
  · exact batch30
  · exact batch31

end Rudvalis.OrderCertificate.OrderLevel2Positive1
