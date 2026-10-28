module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
import Mathlib.Tactic.FinCases

/-!
# Positive-generator-0 transitions: batches 156–169

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
private theorem batch156 : stepBatch 0 156 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch157 : stepBatch 0 157 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch158 : stepBatch 0 158 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch159 : stepBatch 0 159 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch160 : stepBatch 0 160 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch161 : stepBatch 0 161 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch162 : stepBatch 0 162 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch163 : stepBatch 0 163 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch164 : stepBatch 0 164 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch165 : stepBatch 0 165 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch166 : stepBatch 0 166 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch167 : stepBatch 0 167 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch168 : stepBatch 0 168 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch169 : stepBatch 0 169 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The fourteen batches starting at 156 satisfy the transition identity. -/
public theorem part4 (b : Fin 14) : stepBatch 0 ⟨156 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch156
  · exact batch157
  · exact batch158
  · exact batch159
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

end Rudvalis.OrderCertificate.OrderLevel1Positive0.BlockB
