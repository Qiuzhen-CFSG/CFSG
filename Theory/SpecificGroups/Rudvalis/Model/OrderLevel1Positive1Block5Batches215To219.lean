module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block5Batches210To214
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 215–219

This certifies representatives 1075–1099 by free cancellation or, when
necessary, equality on all 4060 points checked in Lean's kernel. The supporting
modules form a sequential chain so completed groups are reusable build artifacts.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch215 : stepBatch 1 215 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch216 : stepBatch 1 216 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch217 : stepBatch 1 217 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch218 : stepBatch 1 218 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch219 : stepBatch 1 219 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 215 through 219. -/
public theorem segment215 (b : Fin 5) :
    stepBatch 1 ⟨215 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch215
  · exact batch216
  · exact batch217
  · exact batch218
  · exact batch219

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
