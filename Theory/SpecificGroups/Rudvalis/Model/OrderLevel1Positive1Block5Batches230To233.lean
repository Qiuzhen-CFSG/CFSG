module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block5Batches225To229
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 230–233

This certifies representatives 1150–1169 by free cancellation or, when
necessary, equality on all 4060 points checked in Lean's kernel. The supporting
modules form a sequential chain so completed groups are reusable build artifacts.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch230 : stepBatch 1 230 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch231 : stepBatch 1 231 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch232 : stepBatch 1 232 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch233 : stepBatch 1 233 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 230 through 233. -/
public theorem segment230 (b : Fin 4) :
    stepBatch 1 ⟨230 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch230
  · exact batch231
  · exact batch232
  · exact batch233

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block5
