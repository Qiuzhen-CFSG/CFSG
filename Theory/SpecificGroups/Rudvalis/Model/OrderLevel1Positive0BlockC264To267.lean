module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Reduction
import Mathlib.Tactic.FinCases

/-!
# Positive level-1 Rudvalis transitions: batches 264–267

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
private theorem batch264 : stepBatch 0 264 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch265 : stepBatch 0 265 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch266 : stepBatch 0 266 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch267 : stepBatch 0 267 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-0 transitions for batches 264 through 267. -/
public theorem segment264 (b : Fin 4) :
    stepBatch 0 ⟨264 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch264
  · exact batch265
  · exact batch266
  · exact batch267

end Rudvalis.OrderCertificate.OrderLevel1Positive0
