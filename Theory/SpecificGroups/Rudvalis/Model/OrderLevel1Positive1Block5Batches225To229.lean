module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block5Batches220To224
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 225–229

This certifies representatives 1125–1149 by free cancellation or, when
necessary, equality on all 4060 points checked in Lean's kernel. The supporting
modules form a sequential chain so completed groups are reusable build artifacts.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch225 : stepBatch 1 225 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch226 : stepBatch 1 226 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch227 : stepBatch 1 227 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch228 : stepBatch 1 228 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch229 : stepBatch 1 229 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 225 through 229. -/
public theorem segment225 (b : Fin 5) :
    stepBatch 1 ⟨225 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch225
  · exact batch226
  · exact batch227
  · exact batch228
  · exact batch229

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
