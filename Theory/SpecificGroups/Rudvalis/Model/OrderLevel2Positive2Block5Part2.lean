module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 2: batches 176-183

The eight transition batches are certified by free cancellation or by
kernel-checked equality on all 4060 permutation points.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2.Block5.Part2
open Level2Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch176 : stepBatch 2 176 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch177 : stepBatch 2 177 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch178 : stepBatch 2 178 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch179 : stepBatch 2 179 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch180 : stepBatch 2 180 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch181 : stepBatch 2 181 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch182 : stepBatch 2 182 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch183 : stepBatch 2 183 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The eight batches from 176 through 183. -/
public theorem batches (b : Fin 8) :
    stepBatch 2 ⟨160 + 8 * 2 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch176
  · exact batch177
  · exact batch178
  · exact batch179
  · exact batch180
  · exact batch181
  · exact batch182
  · exact batch183

end Rudvalis.OrderCertificate.OrderLevel2Positive2.Block5.Part2

