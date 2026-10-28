module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
import Mathlib.Tactic.FinCases

/-!
# Positive-generator-0 transitions: batches 142–155

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
private theorem batch142 : stepBatch 0 142 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch143 : stepBatch 0 143 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch144 : stepBatch 0 144 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch145 : stepBatch 0 145 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch146 : stepBatch 0 146 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch147 : stepBatch 0 147 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch148 : stepBatch 0 148 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch149 : stepBatch 0 149 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch150 : stepBatch 0 150 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch151 : stepBatch 0 151 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch152 : stepBatch 0 152 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch153 : stepBatch 0 153 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch154 : stepBatch 0 154 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch155 : stepBatch 0 155 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The fourteen batches starting at 142 satisfy the transition identity. -/
public theorem part3 (b : Fin 14) : stepBatch 0 ⟨142 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch142
  · exact batch143
  · exact batch144
  · exact batch145
  · exact batch146
  · exact batch147
  · exact batch148
  · exact batch149
  · exact batch150
  · exact batch151
  · exact batch152
  · exact batch153
  · exact batch154
  · exact batch155

end Rudvalis.OrderCertificate.OrderLevel1Positive0.BlockB
