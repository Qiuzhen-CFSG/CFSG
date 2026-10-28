module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 195–199

This certifies representatives 975–999 by free cancellation or, when
necessary, equality on all 4060 points checked in Lean's kernel. The supporting
modules form a sequential chain so completed groups are reusable build artifacts.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch195 : stepBatch 1 195 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch196 : stepBatch 1 196 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch197 : stepBatch 1 197 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch198 : stepBatch 1 198 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch199 : stepBatch 1 199 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 195 through 199. -/
public theorem segment195 (b : Fin 5) :
    stepBatch 1 ⟨195 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch195
  · exact batch196
  · exact batch197
  · exact batch198
  · exact batch199

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
