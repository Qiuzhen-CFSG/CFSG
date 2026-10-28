module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 2: batches 224-255

Each remaining batch is checked pointwise on the 4060 permutation points by
Lean's kernel.  Cancellation-only batches are discharged by the shared reduction.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2.Block7
open Level2Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch224 : stepBatch 2 224 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch225 : stepBatch 2 225 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch226 : stepBatch 2 226 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch227 : stepBatch 2 227 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch228 : stepBatch 2 228 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch229 : stepBatch 2 229 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch230 : stepBatch 2 230 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch231 : stepBatch 2 231 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch232 : stepBatch 2 232 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch233 : stepBatch 2 233 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch234 : stepBatch 2 234 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch235 : stepBatch 2 235 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch236 : stepBatch 2 236 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch237 : stepBatch 2 237 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch238 : stepBatch 2 238 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch239 : stepBatch 2 239 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch240 : stepBatch 2 240 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch241 : stepBatch 2 241 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch242 : stepBatch 2 242 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch243 : stepBatch 2 243 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch244 : stepBatch 2 244 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch245 : stepBatch 2 245 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch246 : stepBatch 2 246 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch247 : stepBatch 2 247 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch248 : stepBatch 2 248 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch249 : stepBatch 2 249 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch250 : stepBatch 2 250 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch251 : stepBatch 2 251 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch252 : stepBatch 2 252 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch253 : stepBatch 2 253 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch254 : stepBatch 2 254 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch255 : stepBatch 2 255 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The thirty-two batches from 224 through 255. -/
public theorem batches (b : Fin 32) : stepBatch 2 ⟨224 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch224
  · exact batch225
  · exact batch226
  · exact batch227
  · exact batch228
  · exact batch229
  · exact batch230
  · exact batch231
  · exact batch232
  · exact batch233
  · exact batch234
  · exact batch235
  · exact batch236
  · exact batch237
  · exact batch238
  · exact batch239
  · exact batch240
  · exact batch241
  · exact batch242
  · exact batch243
  · exact batch244
  · exact batch245
  · exact batch246
  · exact batch247
  · exact batch248
  · exact batch249
  · exact batch250
  · exact batch251
  · exact batch252
  · exact batch253
  · exact batch254
  · exact batch255

end Rudvalis.OrderCertificate.OrderLevel2Positive2.Block7
