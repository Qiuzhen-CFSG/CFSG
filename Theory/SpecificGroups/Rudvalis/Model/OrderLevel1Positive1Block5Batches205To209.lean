module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block5Batches200To204
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 205–209

This certifies representatives 1025–1049 by free cancellation or, when
necessary, equality on all 4060 points checked in Lean's kernel. The supporting
modules form a sequential chain so completed groups are reusable build artifacts.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch205 : stepBatch 1 205 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch206 : stepBatch 1 206 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch207 : stepBatch 1 207 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch208 : stepBatch 1 208 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch209 : stepBatch 1 209 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 205 through 209. -/
public theorem segment205 (b : Fin 5) :
    stepBatch 1 ⟨205 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch205
  · exact batch206
  · exact batch207
  · exact batch208
  · exact batch209

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
