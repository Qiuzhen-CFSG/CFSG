module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 2: batches 184-191

The eight transition batches are certified by free cancellation or by
kernel-checked equality on all 4060 permutation points.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2.Block5.Part3
open Level2Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch184 : stepBatch 2 184 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch185 : stepBatch 2 185 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch186 : stepBatch 2 186 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch187 : stepBatch 2 187 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch188 : stepBatch 2 188 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch189 : stepBatch 2 189 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch190 : stepBatch 2 190 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch191 : stepBatch 2 191 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The eight batches from 184 through 191. -/
public theorem batches (b : Fin 8) :
    stepBatch 2 ⟨160 + 8 * 3 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch184
  · exact batch185
  · exact batch186
  · exact batch187
  · exact batch188
  · exact batch189
  · exact batch190
  · exact batch191

end Rudvalis.OrderCertificate.OrderLevel2Positive2.Block5.Part3

