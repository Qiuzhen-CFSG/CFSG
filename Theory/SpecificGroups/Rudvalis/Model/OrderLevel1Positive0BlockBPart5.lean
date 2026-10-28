module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
import Mathlib.Tactic.FinCases

/-!
# Positive-generator-0 transitions: batches 170–183

Each batch certifies five level-1 orbit representatives by free cancellation or
pointwise equality on all 4060 points, checked in Lean's kernel. These bounded
compilation units checkpoint the certificate assembled in
`OrderLevel1Positive0BlockB`.

Source: the ATLAS-derived witnesses documented in `OrderLevel1Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0.BlockB
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch170 : stepBatch 0 170 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch171 : stepBatch 0 171 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch172 : stepBatch 0 172 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch173 : stepBatch 0 173 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch174 : stepBatch 0 174 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch175 : stepBatch 0 175 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch176 : stepBatch 0 176 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch177 : stepBatch 0 177 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch178 : stepBatch 0 178 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch179 : stepBatch 0 179 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch180 : stepBatch 0 180 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch181 : stepBatch 0 181 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch182 : stepBatch 0 182 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch183 : stepBatch 0 183 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The fourteen batches starting at 170 satisfy the transition identity. -/
public theorem part5 (b : Fin 14) : stepBatch 0 ⟨170 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch170
  · exact batch171
  · exact batch172
  · exact batch173
  · exact batch174
  · exact batch175
  · exact batch176
  · exact batch177
  · exact batch178
  · exact batch179
  · exact batch180
  · exact batch181
  · exact batch182
  · exact batch183

end Rudvalis.OrderCertificate.OrderLevel1Positive0.BlockB
