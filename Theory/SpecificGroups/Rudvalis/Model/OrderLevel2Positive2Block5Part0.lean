module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 2: batches 160-167

The eight transition batches are certified by free cancellation or by
kernel-checked equality on all 4060 permutation points.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2.Block5.Part0
open Level2Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch160 : stepBatch 2 160 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch161 : stepBatch 2 161 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch162 : stepBatch 2 162 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch163 : stepBatch 2 163 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch164 : stepBatch 2 164 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch165 : stepBatch 2 165 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch166 : stepBatch 2 166 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch167 : stepBatch 2 167 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The eight batches from 160 through 167. -/
public theorem batches (b : Fin 8) :
    stepBatch 2 ⟨160 + 8 * 0 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch160
  · exact batch161
  · exact batch162
  · exact batch163
  · exact batch164
  · exact batch165
  · exact batch166
  · exact batch167

end Rudvalis.OrderCertificate.OrderLevel2Positive2.Block5.Part0

