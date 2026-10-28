module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
import Mathlib.Tactic.FinCases

/-!
# First block of positive level-1 Rudvalis transitions

This certifies batches 0 through 15, each containing five orbit representatives.
The checker uses free cancellation where possible and otherwise verifies equality
at all 4060 points in Lean's kernel. The permutation and word witnesses are the
ATLAS-derived data documented in `OrderLevel1Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch0 : stepBatch 0 0 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch1 : stepBatch 0 1 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch2 : stepBatch 0 2 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch3 : stepBatch 0 3 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch4 : stepBatch 0 4 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch5 : stepBatch 0 5 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch6 : stepBatch 0 6 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch7 : stepBatch 0 7 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch8 : stepBatch 0 8 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch9 : stepBatch 0 9 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch10 : stepBatch 0 10 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch11 : stepBatch 0 11 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch12 : stepBatch 0 12 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch13 : stepBatch 0 13 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch14 : stepBatch 0 14 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch15 : stepBatch 0 15 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The first eighty representatives satisfy the positive transition identity. -/
public theorem initial (b : Fin 16) : stepBatch 0 (b.castLE (by decide)) := by
  fin_cases b
  · exact batch0
  · exact batch1
  · exact batch2
  · exact batch3
  · exact batch4
  · exact batch5
  · exact batch6
  · exact batch7
  · exact batch8
  · exact batch9
  · exact batch10
  · exact batch11
  · exact batch12
  · exact batch13
  · exact batch14
  · exact batch15

end Rudvalis.OrderCertificate.OrderLevel1Positive0
