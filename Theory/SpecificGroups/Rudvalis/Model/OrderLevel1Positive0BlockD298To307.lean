module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive0BlockD268To277
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions: batches 298–307

This checkpoint certifies the five representatives in each indicated batch for
positive generator 0. The checker proves free word cancellation or checks the
permutations at all 4060 points in Lean's kernel. Checkpoints are imported in three
chains to bound concurrent memory-intensive checks during a combined Lake build.

Source: the ATLAS-derived witnesses documented in `OrderLevel1Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive0
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch298 : stepBatch 0 298 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch299 : stepBatch 0 299 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch300 : stepBatch 0 300 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch301 : stepBatch 0 301 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch302 : stepBatch 0 302 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch303 : stepBatch 0 303 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch304 : stepBatch 0 304 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch305 : stepBatch 0 305 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch306 : stepBatch 0 306 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch307 : stepBatch 0 307 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-0 transitions for batches 298 through 307. -/
public theorem segment298 (b : Fin 10) :
    stepBatch 0 ⟨298 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch298
  · exact batch299
  · exact batch300
  · exact batch301
  · exact batch302
  · exact batch303
  · exact batch304
  · exact batch305
  · exact batch306
  · exact batch307

end Rudvalis.OrderCertificate.OrderLevel1Positive0
