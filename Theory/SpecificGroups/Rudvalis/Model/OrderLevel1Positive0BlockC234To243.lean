module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions: batches 234–243

This checkpoint certifies the five representatives in each indicated batch for
positive generator 0. The checker proves free word cancellation or checks the
permutations at all 4060 points in Lean's kernel.

Source: the ATLAS-derived witnesses documented in `OrderLevel1Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch234 : stepBatch 0 234 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch235 : stepBatch 0 235 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch236 : stepBatch 0 236 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch237 : stepBatch 0 237 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch238 : stepBatch 0 238 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch239 : stepBatch 0 239 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch240 : stepBatch 0 240 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch241 : stepBatch 0 241 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch242 : stepBatch 0 242 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch243 : stepBatch 0 243 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-0 transitions for batches 234 through 243. -/
public theorem segment234 (b : Fin 10) :
    stepBatch 0 ⟨234 + b.val, by omega⟩ := by
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

end Rudvalis.OrderCertificate.OrderLevel1Positive0
