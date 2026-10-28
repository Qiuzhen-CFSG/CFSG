module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Reduction
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 317–321

This certifies representatives 1585–1609. Each batch uses the proved free
cancellation or pointwise permutation checker from `OrderLevel1Reduction`.
The latter checks equality on all 4060 points in Lean's kernel. The five batch
proofs elaborate sequentially and assemble into a certificate for this range.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch317 : stepBatch 1 317 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch318 : stepBatch 1 318 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch319 : stepBatch 1 319 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch320 : stepBatch 1 320 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch321 : stepBatch 1 321 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 317 through 321. -/
public theorem segment317 (b : Fin 5) :
    stepBatch 1 ⟨317 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch317
  · exact batch318
  · exact batch319
  · exact batch320
  · exact batch321

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
