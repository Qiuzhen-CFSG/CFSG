module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 200–204

This certifies representatives 1000–1024 by free cancellation or, when
necessary, equality on all 4060 points checked in Lean's kernel. The supporting
modules form a sequential chain so completed groups are reusable build artifacts.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch200 : stepBatch 1 200 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch201 : stepBatch 1 201 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch202 : stepBatch 1 202 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch203 : stepBatch 1 203 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch204 : stepBatch 1 204 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 200 through 204. -/
public theorem segment200 (b : Fin 5) :
    stepBatch 1 ⟨200 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch200
  · exact batch201
  · exact batch202
  · exact batch203
  · exact batch204

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
