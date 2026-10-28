module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
import Mathlib.Tactic.FinCases

/-!
# Seventh block for the second positive Rudvalis level-1 generator

This certifies batches 234-272, covering representatives 1170-1364. Every
batch first tries proved free cancellation and otherwise checks all 4060
permutation points in Lean's kernel, five representatives at a time. The
39 batches are then assembled into the block certificate.

Source: the ATLAS-derived witnesses in OrderLevel1Data and OrderChainData,
as documented by OrderCertificate/GenerateChain.g and
OrderCertificate/GenerateFactors.g.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch234 : stepBatch 1 234 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch235 : stepBatch 1 235 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch236 : stepBatch 1 236 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch237 : stepBatch 1 237 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch238 : stepBatch 1 238 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch239 : stepBatch 1 239 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch240 : stepBatch 1 240 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch241 : stepBatch 1 241 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch242 : stepBatch 1 242 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch243 : stepBatch 1 243 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch244 : stepBatch 1 244 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch245 : stepBatch 1 245 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch246 : stepBatch 1 246 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch247 : stepBatch 1 247 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch248 : stepBatch 1 248 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch249 : stepBatch 1 249 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch250 : stepBatch 1 250 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch251 : stepBatch 1 251 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch252 : stepBatch 1 252 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch253 : stepBatch 1 253 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch254 : stepBatch 1 254 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch255 : stepBatch 1 255 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch256 : stepBatch 1 256 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch257 : stepBatch 1 257 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch258 : stepBatch 1 258 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch259 : stepBatch 1 259 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch260 : stepBatch 1 260 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch261 : stepBatch 1 261 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch262 : stepBatch 1 262 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch263 : stepBatch 1 263 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch264 : stepBatch 1 264 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch265 : stepBatch 1 265 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch266 : stepBatch 1 266 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch267 : stepBatch 1 267 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch268 : stepBatch 1 268 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch269 : stepBatch 1 269 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch270 : stepBatch 1 270 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch271 : stepBatch 1 271 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch272 : stepBatch 1 272 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- All 39 batches in the seventh block satisfy the required identity. -/
public theorem block6 : block 6 := by
  intro b
  fin_cases b
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
  · exact batch256
  · exact batch257
  · exact batch258
  · exact batch259
  · exact batch260
  · exact batch261
  · exact batch262
  · exact batch263
  · exact batch264
  · exact batch265
  · exact batch266
  · exact batch267
  · exact batch268
  · exact batch269
  · exact batch270
  · exact batch271
  · exact batch272

end Rudvalis.OrderCertificate.OrderLevel1Positive1

