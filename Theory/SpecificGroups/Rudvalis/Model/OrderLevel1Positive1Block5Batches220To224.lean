module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 220–224

This certifies representatives 1100–1124 by free cancellation or, when
necessary, equality on all 4060 points checked in Lean's kernel. The supporting
modules form a sequential chain so completed groups are reusable build artifacts.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch220 : stepBatch 1 220 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch221 : stepBatch 1 221 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch222 : stepBatch 1 222 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch223 : stepBatch 1 223 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch224 : stepBatch 1 224 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 220 through 224. -/
public theorem segment220 (b : Fin 5) :
    stepBatch 1 ⟨220 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch220
  · exact batch221
  · exact batch222
  · exact batch223
  · exact batch224

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
