module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Positive1Block8Batches327To331
import Mathlib.Tactic.FinCases

/-!
# Second positive Rudvalis level-1 transition: batches 332–336

This certifies representatives 1660–1684. Each batch first uses proved free
cancellation when available and otherwise checks equality on all 4060 points
in Lean's kernel. The five batch proofs elaborate sequentially and assemble
into a certificate for this bounded range.

Source: the ATLAS witnesses in `OrderLevel1Data` and `OrderChainData`, generated
by `OrderCertificate/GenerateChain.g` and `OrderCertificate/GenerateFactors.g`;
checker correctness is proved in `OrderLevel1Reduction`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
open Level1Reduction
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem batch332 : stepBatch 1 332 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch333 : stepBatch 1 333 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch334 : stepBatch 1 334 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch335 : stepBatch 1 335 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem batch336 : stepBatch 1 336 := by
  apply ofStepBatchCheck
  apply allFin
  decide +kernel

/-- The positive-generator-1 transitions for batches 332 through 336. -/
public theorem segment332 (b : Fin 5) :
    stepBatch 1 ⟨332 + b.val, by omega⟩ := by
  fin_cases b
  · exact batch332
  · exact batch333
  · exact batch334
  · exact batch335
  · exact batch336

end Rudvalis.OrderCertificate.OrderLevel1Positive1.Block8
