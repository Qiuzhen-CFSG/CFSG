module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions, batches 184–195

Each batch verifies five orbit representatives by free cancellation or kernel
checking on all 4060 points. These compilation checkpoints use the ATLAS-derived
witnesses documented in `OrderLevel1Data` and `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0.BlockC
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch184 : stepBatch 0 184 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch185 : stepBatch 0 185 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch186 : stepBatch 0 186 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch187 : stepBatch 0 187 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch188 : stepBatch 0 188 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch189 : stepBatch 0 189 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch190 : stepBatch 0 190 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch191 : stepBatch 0 191 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch192 : stepBatch 0 192 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch193 : stepBatch 0 193 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch194 : stepBatch 0 194 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch195 : stepBatch 0 195 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- Positive-generator-0 transitions for batches 184 through 195. -/
public theorem part0 (b : Fin 12) : stepBatch 0 ⟨184 + b.val, by omega⟩ := by
  fin_cases b
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
  · exact batch195

end Rudvalis.OrderCertificate.OrderLevel1Positive0.BlockC
