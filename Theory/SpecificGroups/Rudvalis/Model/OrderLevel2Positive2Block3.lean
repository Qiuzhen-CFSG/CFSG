module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 2: batches 96-127

Each remaining batch is checked pointwise on the 4060 permutation points by
Lean's kernel.  Cancellation-only batches are discharged by the shared reduction.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2.Block3
open Level2Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch96 : stepBatch 2 96 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch97 : stepBatch 2 97 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch98 : stepBatch 2 98 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch99 : stepBatch 2 99 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch100 : stepBatch 2 100 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch101 : stepBatch 2 101 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch102 : stepBatch 2 102 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch103 : stepBatch 2 103 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch104 : stepBatch 2 104 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch105 : stepBatch 2 105 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch106 : stepBatch 2 106 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch107 : stepBatch 2 107 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch108 : stepBatch 2 108 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch109 : stepBatch 2 109 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch110 : stepBatch 2 110 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch112 : stepBatch 2 112 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch113 : stepBatch 2 113 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch114 : stepBatch 2 114 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch115 : stepBatch 2 115 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch116 : stepBatch 2 116 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch117 : stepBatch 2 117 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch118 : stepBatch 2 118 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch119 : stepBatch 2 119 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch120 : stepBatch 2 120 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch121 : stepBatch 2 121 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch122 : stepBatch 2 122 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch123 : stepBatch 2 123 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch124 : stepBatch 2 124 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch125 : stepBatch 2 125 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch126 : stepBatch 2 126 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch127 : stepBatch 2 127 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The thirty-two batches from 96 through 127. -/
public theorem batches (b : Fin 32) : stepBatch 2 ⟨96 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch96
  · exact batch97
  · exact batch98
  · exact batch99
  · exact batch100
  · exact batch101
  · exact batch102
  · exact batch103
  · exact batch104
  · exact batch105
  · exact batch106
  · exact batch107
  · exact batch108
  · exact batch109
  · exact batch110
  · exact algebraic_batches 111 (by decide +kernel)
  · exact batch112
  · exact batch113
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

end Rudvalis.OrderCertificate.OrderLevel2Positive2.Block3
