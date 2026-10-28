module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
import Mathlib.Tactic.FinCases

/-!
# Positive-generator-0 transitions: batches 114–127

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
private theorem batch114 : stepBatch 0 114 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch115 : stepBatch 0 115 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch116 : stepBatch 0 116 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch117 : stepBatch 0 117 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch118 : stepBatch 0 118 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch119 : stepBatch 0 119 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch120 : stepBatch 0 120 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch121 : stepBatch 0 121 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch122 : stepBatch 0 122 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch123 : stepBatch 0 123 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch124 : stepBatch 0 124 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch125 : stepBatch 0 125 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch126 : stepBatch 0 126 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch127 : stepBatch 0 127 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The fourteen batches starting at 114 satisfy the transition identity. -/
public theorem part1 (b : Fin 14) : stepBatch 0 ⟨114 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch114
  · exact batch115
  · exact batch116
  · exact batch117
  · exact batch118
  · exact batch119
  · exact batch120
  · exact batch121
  · exact batch122
  · exact batch123
  · exact batch124
  · exact batch125
  · exact batch126
  · exact batch127

end Rudvalis.OrderCertificate.OrderLevel1Positive0.BlockB
