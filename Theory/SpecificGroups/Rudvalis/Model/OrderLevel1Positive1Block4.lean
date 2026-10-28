module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
import Mathlib.Tactic.FinCases

/-!
# Fifth block for the second positive Rudvalis level-1 generator

This certifies batches 156–194, covering representatives 780–974. Each batch
first checks free cancellation and otherwise checks the transition on all 4060
points in Lean's kernel. The 39 certificates assemble into `block 4`.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, with the
checker correctness proved in `OrderLevel1Reduction`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch156 : stepBatch 1 156 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch157 : stepBatch 1 157 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch158 : stepBatch 1 158 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch159 : stepBatch 1 159 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch160 : stepBatch 1 160 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch161 : stepBatch 1 161 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch162 : stepBatch 1 162 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch163 : stepBatch 1 163 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch164 : stepBatch 1 164 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch165 : stepBatch 1 165 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch166 : stepBatch 1 166 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch167 : stepBatch 1 167 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch168 : stepBatch 1 168 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch169 : stepBatch 1 169 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch170 : stepBatch 1 170 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch171 : stepBatch 1 171 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch172 : stepBatch 1 172 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch173 : stepBatch 1 173 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch174 : stepBatch 1 174 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch175 : stepBatch 1 175 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch176 : stepBatch 1 176 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch177 : stepBatch 1 177 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch178 : stepBatch 1 178 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch179 : stepBatch 1 179 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch180 : stepBatch 1 180 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch181 : stepBatch 1 181 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch182 : stepBatch 1 182 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch183 : stepBatch 1 183 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch184 : stepBatch 1 184 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch185 : stepBatch 1 185 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch186 : stepBatch 1 186 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch187 : stepBatch 1 187 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch188 : stepBatch 1 188 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch189 : stepBatch 1 189 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch190 : stepBatch 1 190 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch191 : stepBatch 1 191 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch192 : stepBatch 1 192 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch193 : stepBatch 1 193 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch194 : stepBatch 1 194 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- Positive generator 1 satisfies the transitions in batches 156–194. -/
public theorem block4 : block 4 := by
  intro b
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
  · exact batch184
  · exact batch185
  · exact batch186
  · exact batch187
  · exact batch188
  · exact batch189
  · exact batch190
  · exact batch191
  · exact batch192
  · exact batch193
  · exact batch194

end Rudvalis.OrderCertificate.OrderLevel1Positive1
