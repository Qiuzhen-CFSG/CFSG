module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 2: batches 128-159

Each remaining batch is checked pointwise on the 4060 permutation points by
Lean's kernel.  Cancellation-only batches are discharged by the shared reduction.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2.Block4
open Level2Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch128 : stepBatch 2 128 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch129 : stepBatch 2 129 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch130 : stepBatch 2 130 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch131 : stepBatch 2 131 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch132 : stepBatch 2 132 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch133 : stepBatch 2 133 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch134 : stepBatch 2 134 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch135 : stepBatch 2 135 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch136 : stepBatch 2 136 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch137 : stepBatch 2 137 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch138 : stepBatch 2 138 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch139 : stepBatch 2 139 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch140 : stepBatch 2 140 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch141 : stepBatch 2 141 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch142 : stepBatch 2 142 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch143 : stepBatch 2 143 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch144 : stepBatch 2 144 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch145 : stepBatch 2 145 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch146 : stepBatch 2 146 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch147 : stepBatch 2 147 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch148 : stepBatch 2 148 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch149 : stepBatch 2 149 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch150 : stepBatch 2 150 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch151 : stepBatch 2 151 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch152 : stepBatch 2 152 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch153 : stepBatch 2 153 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch154 : stepBatch 2 154 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch155 : stepBatch 2 155 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch156 : stepBatch 2 156 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch157 : stepBatch 2 157 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch158 : stepBatch 2 158 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch159 : stepBatch 2 159 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The thirty-two batches from 128 through 159. -/
public theorem batches (b : Fin 32) : stepBatch 2 ⟨128 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch128
  · exact batch129
  · exact batch130
  · exact batch131
  · exact batch132
  · exact batch133
  · exact batch134
  · exact batch135
  · exact batch136
  · exact batch137
  · exact batch138
  · exact batch139
  · exact batch140
  · exact batch141
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
  · exact batch156
  · exact batch157
  · exact batch158
  · exact batch159

end Rudvalis.OrderCertificate.OrderLevel2Positive2.Block4
