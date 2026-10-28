module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Positive2Reduction
import Mathlib.Tactic.FinCases

/-!
# Rudvalis level-2 generator 2: batches 168-175

The eight transition batches are certified by free cancellation or by
kernel-checked equality on all 4060 permutation points.

Source: the ATLAS witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2.Block5.Part1
open Level2Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch168 : stepBatch 2 168 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch169 : stepBatch 2 169 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch170 : stepBatch 2 170 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch171 : stepBatch 2 171 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch172 : stepBatch 2 172 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch173 : stepBatch 2 173 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch174 : stepBatch 2 174 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch175 : stepBatch 2 175 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The eight batches from 168 through 175. -/
public theorem batches (b : Fin 8) :
    stepBatch 2 ⟨160 + 8 * 1 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch168
  · exact batch169
  · exact batch170
  · exact batch171
  · exact batch172
  · exact batch173
  · exact batch174
  · exact batch175

end Rudvalis.OrderCertificate.OrderLevel2Positive2.Block5.Part1

