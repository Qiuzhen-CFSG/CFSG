module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 0: representatives 768–831

The sixteen batches below certify the forward transition on this range.
Free cancellation is attempted first; all remaining permutation equalities
are checked on all 4060 points by the Lean kernel.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive0
open Level2Reduction
set_option Elab.async false

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

set_option maxRecDepth 30000 in
private theorem batch196 : stepBatch 0 196 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch197 : stepBatch 0 197 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch198 : stepBatch 0 198 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch199 : stepBatch 0 199 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch200 : stepBatch 0 200 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch201 : stepBatch 0 201 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch202 : stepBatch 0 202 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch203 : stepBatch 0 203 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch204 : stepBatch 0 204 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch205 : stepBatch 0 205 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch206 : stepBatch 0 206 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch207 : stepBatch 0 207 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- Generator 0 transitions for representatives 768 through 831. -/
public theorem block12 : ∀ s : Fin 16,
    stepBatch 0 ⟨16 * 12 + s.val, by omega⟩ := by
  intro s
  fin_cases s
  · exact batch192
  · exact batch193
  · exact batch194
  · exact batch195
  · exact batch196
  · exact batch197
  · exact batch198
  · exact batch199
  · exact batch200
  · exact batch201
  · exact batch202
  · exact batch203
  · exact batch204
  · exact batch205
  · exact batch206
  · exact batch207

end Rudvalis.OrderCertificate.OrderLevel2Positive0
