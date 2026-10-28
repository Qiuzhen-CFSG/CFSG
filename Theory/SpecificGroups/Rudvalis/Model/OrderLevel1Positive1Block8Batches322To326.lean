module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block8Batches317To321
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 322–326

This certifies representatives 1610–1634. Each batch uses the proved free
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
private theorem batch322 : stepBatch 1 322 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch323 : stepBatch 1 323 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch324 : stepBatch 1 324 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch325 : stepBatch 1 325 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch326 : stepBatch 1 326 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 322 through 326. -/
public theorem segment322 (b : Fin 5) :
    stepBatch 1 ⟨322 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch322
  · exact batch323
  · exact batch324
  · exact batch325
  · exact batch326

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
